import java.io.File;
import java.io.FileNotFoundException;
import java.util.Arrays;
import java.util.Scanner;

public class DES_CFB {

    private static final int BLOCK_SIZE = 8;//размер блока
    private static final int rounds = 16;
    private static byte[] encrypt(byte[] plaintext, byte[] key, byte[] iv) {
        byte[] ciphertext = new byte[plaintext.length];//  массив ciphertext размером
        // равным размеру сообщения plaintext в этот массив будет записываться зашифрованный текст
        byte[] previousBlock = iv.clone();// создаем копию вектора инициализациии iv и присваиваем его переменной previousBlock


        for (int i = 0; i < plaintext.length; i += BLOCK_SIZE) {//цикл, который перебирает блоки данных входного сообщения
            // шаг итерации составляет BLOCK_SIZE
            // что обозначает размер блока данных используемый в алгоритме.
            byte[] encryptedBlock = des(previousBlock, key, false);//выполняет вектора
            // Используем false для шифрования
            int blockSize = Math.min(BLOCK_SIZE, plaintext.length - i);//определяет размер текущего блока данных который может быть меньше размера blocksize

            byte[] block = Arrays.copyOfRange(plaintext, i, i + blockSize);//создаем массив block
            // содержащий текущий блок данных для шифрования этот блок берется из входного сообщения plaintext

            for (int j = 0; j < blockSize; j++) {
                ciphertext[i + j] = (byte) (encryptedBlock[j] ^ block[j]);//начинается цикл, который перебирает каждый байт в текущем блоке данных
            }//выполняем операцию побитового исключающего XOR между зашифрованным предыдущим блоком encryptedBlock и текущим блоком данных block
            // Результат записывается в соответствующий байт массива ciphertext, чтобы получить зашифрованный байт
            // обновление previousBlock на каждой итерации
            previousBlock = Arrays.copyOfRange(ciphertext, i, i + blockSize);
        }

        return ciphertext;
    }

    private static byte[] decrypt(byte[] ciphertext, byte[] key, byte[] iv) {
        byte[] plaintext = new byte[ciphertext.length]; //создаем массив plaintext размером равным размеру зашифрованного текста ciphertext
        // в этот массив будет записываться расшифрованный текст
        byte[] previousBlock = iv.clone();//создаем копию вектора инициализации

        for (int i = 0; i < ciphertext.length; i += BLOCK_SIZE) {//цикл, который перебирает блоки зашифрованного текста
            byte[] encryptedBlock = des(previousBlock, key, false); // используем false для шифрования
            int blockSize = Math.min(BLOCK_SIZE, ciphertext.length - i);

            byte[] block = Arrays.copyOfRange(ciphertext, i, i + blockSize);// моздаем массив block содержащий текущий блок
            // зашифрованного текста для дешифр этот блок берется из зашифрованного текста ciphertext

            for (int j = 0; j < blockSize; j++) {// цикл, который перебирает каждый байт в текущем блоке данных
                plaintext[i + j] = (byte) (encryptedBlock[j] ^ block[j]);//операция побитового исключающего xor между предыдущим зашифрованным блоком encryptedBlock и
                // текущим блоком данных block
                //  ^ xor
            }   //i + j используется для определения позиции в массиве plaintext куда будет записан результат операции хор
                //переменная i представляет собой текущую позицию в массиве ciphertext переменная j представляет относительную позицию внутри текущего блока данных.

            //то есть если BLOCK_SIZE равно 8, то элементы второго блока данных будут записываться в
            // массив plaintext начиная
            // с позиции 8 (те plaintext[8], plaintext[9], plaintext[10] и тд)

            // обновление previousBlock на каждой итерации
            previousBlock = block;
        }

        return plaintext;
    }
    // функция DES шифрования/дешифрования блока
    private static byte[] des(byte[] block, byte[] key, boolean encrypt) {
        // проверка длины ключа
        if (key.length != 8) {
            throw new IllegalArgumentException("ОШИБКА!");
        }
        // генерация подключей
        byte[][] subkeys = generateSubkeys(key);
        // начальная перестановка блока
        block = initialPermutation(block);
        // разделение блока на левую и правую половины
        byte[] leftHalf = Arrays.copyOfRange(block, 0, BLOCK_SIZE / 2);
        byte[] rightHalf = Arrays.copyOfRange(block, BLOCK_SIZE / 2, BLOCK_SIZE);
        // 16 раундов шифрования/дешифрования
        for (int round = 0; round < rounds; round++) {
            byte[] previousLeftHalf = leftHalf.clone();
            // расширение правой половины
            byte[] expandedRightHalf = expansionPermutation(rightHalf);
            // XOR с подключом раунда
            byte[] xorResult = xor(expandedRightHalf, subkeys[round]);
            // Sблоки
            byte[] sBoxResult = sBox(xorResult);
            // перестановка P-бокса
            byte[] pBoxResult = pBoxPermutation(sBoxResult);
            // выполняем операцию xor между двумя массивами в зависимости от значения переменной encrypt
            //ес encrypt равно true то происходит операция между pBoxResult  rightHalf
            //если encrypt равно false то происходит операция между pBoxResult и leftHalf
            byte[] xorResultCFB = encrypt ? xor(pBoxResult, rightHalf) : xor(pBoxResult, leftHalf);
            // обновление левой и правой половин блока
            leftHalf = rightHalf;
            rightHalf = xorResultCFB;
        }
        // объединение правой и левой половин блока
        byte[] twoHalves = new byte[BLOCK_SIZE];
        System.arraycopy(rightHalf, 0, twoHalves, 0, BLOCK_SIZE / 2);
        System.arraycopy(leftHalf, 0, twoHalves, BLOCK_SIZE / 2, BLOCK_SIZE / 2);
        // конечная перестановка блока
        byte[] result = finalPermutation(twoHalves);
        return result;
    }

    // генерация подключей для каждого раунда 16
    private static byte[][] generateSubkeys(byte[] key) {
        byte[][] subkeys = new byte[rounds][BLOCK_SIZE];//Создается двумерный массив subkeys, который будет содержать все подключи.
                                                        // Размерность массива определяется числом раундов
        byte[] permutedKey = permutationKey(key);//Исходный ключ подвергается перестановке (permutationKey), чтобы защитить
        byte[] leftHalf = Arrays.copyOfRange(permutedKey, 0, BLOCK_SIZE / 2);//Берется левая половина permutedKey
                                                                                        // Размер этой половины равен половине размера блока
        byte[] rightHalf = Arrays.copyOfRange(permutedKey, BLOCK_SIZE / 2, BLOCK_SIZE);//аналогично
        for (int round = 0; round < rounds; round++) {//цикл по раундам шифрования round-номер текущего раунда.
            int shift = (round == 0 || round == 1 || round == 8 || round == 15) ? 1 : 2;//вычисляем значение сдвига shift.
            // если номер раунда равен 0, 1, 8 или 15, то сдвиг равен 1 в пр случае сдвиг равен 2
            leftHalf = LeftShift(leftHalf, shift);//левая и права половина  циклически  сдвиг влево на количество бит
            // указанное в shift разнообразие подключей для каждого раунда.
            rightHalf = LeftShift(rightHalf, shift);//аналогично
            byte[] roundKey = new byte[BLOCK_SIZE];//создается временный массив roundKey для хранения подключа текущего раунда
            System.arraycopy(leftHalf, 0, roundKey, 0, BLOCK_SIZE / 2);//евая половина ключа копируется в roundKey
            System.arraycopy(rightHalf, 0, roundKey, BLOCK_SIZE / 2, BLOCK_SIZE / 2);//правая копируетс с позиции после левой половинки
            subkeys[round] = permutationKey(roundKey);//полученный подключ текущего раунда roundKey
            // подвергается перестановке permutationKey результат сохраняется в соответствующем элементе массива
        }
        return subkeys;
    }
    // начальная перестановка блока
    private static byte[] initialPermutation(byte[] block) {
        byte[] result = new byte[BLOCK_SIZE];
        result[0] = block[1];//перестановка
        result[1] = block[5];
        result[2] = block[2];
        result[3] = block[0];
        result[4] = block[3];
        result[5] = block[7];
        result[6] = block[4];
        result[7] = block[6];
        return result;
    }
    // конечная перестановка блока
    private static byte[] finalPermutation(byte[] block) {
        byte[] result = new byte[BLOCK_SIZE];
        result[0] = block[3];//перестановка
        result[1] = block[0];
        result[2] = block[2];
        result[3] = block[4];
        result[4] = block[6];
        result[5] = block[1];
        result[6] = block[7];
        result[7] = block[5];
        return result;
    }

    // расширение правой половины блока
    private static byte[] expansionPermutation(byte[] rightHalf) {//расширение увеличивает половину блока
        // из его исходного размера в больший  добавляя дополнительные биты
        byte[] result = new byte[BLOCK_SIZE];
        result[0] = rightHalf[3];//перестановка
        result[1] = rightHalf[0];
        result[2] = rightHalf[1];
        result[3] = rightHalf[2];
        result[4] = rightHalf[1];
        result[5] = rightHalf[2];
        result[6] = rightHalf[3];
        result[7] = rightHalf[0];
        return result;
    }
    // перестановка пбокса
    private static byte[] pBoxPermutation(byte[] block) {
        byte[] result = new byte[BLOCK_SIZE];
        result[0] = block[1];//расширение
        result[1] = block[3];
        result[2] = block[2];
        result[3] = block[0];
        result[4] = block[3];
        result[5] = block[2];
        result[6] = block[1];
        result[7] = block[0];
        return result;
    }

    // S-блоки
    private static byte[] sBox(byte[] block) {
        byte[] result = new byte[BLOCK_SIZE / 2];
        final int[][] S1 = {
                {14, 4, 13, 1, 2, 15, 11, 8, 3, 10, 6, 12, 5, 9, 0, 7},// инициализируем 8 блоков
                {0, 15, 7, 4, 14, 2, 13, 1, 10, 6, 12, 11, 9, 5, 3, 8},
                {4, 1, 14, 8, 13, 6, 2, 11, 15, 12, 9, 7, 3, 10, 5, 0},
                {15, 12, 8, 2, 4, 9, 1, 7, 5, 11, 3, 14, 10, 0, 6, 13}
        };
         final int[][] S2 = {
                {15, 1, 8, 14, 6, 11, 3, 4, 9, 7, 2, 13, 12, 0, 5, 10},
                {3, 13, 4, 7, 15, 2, 8, 14, 12, 0, 1, 10, 6, 9, 11, 5},
                {0, 14, 7, 11, 10, 4, 13, 1, 5, 8, 12, 6, 9, 3, 2, 15},
                {13, 8, 10, 1, 3, 15, 4, 2, 11, 6, 7, 12, 0, 5, 14, 9}
        };

         final int[][] S3 = {
                {10, 0, 9, 14, 6, 3, 15, 5, 1, 13, 12, 7, 11, 4, 2, 8},
                {13, 7, 0, 9, 3, 4, 6, 10, 2, 8, 5, 14, 12, 11, 15, 1},
                {13, 6, 4, 9, 8, 15, 3, 0, 11, 1, 2, 12, 5, 10, 14, 7},
                {1, 10, 13, 0, 6, 9, 8, 7, 4, 15, 14, 3, 11, 5, 2, 12}
        };

        final int[][] S4 = {
                {7, 13, 14, 3, 0, 6, 9, 10, 1, 2, 8, 5, 11, 12, 4, 15},
                {13, 8, 11, 5, 6, 15, 0, 3, 4, 7, 2, 12, 1, 10, 14, 9},
                {10, 6, 9, 0, 12, 11, 7, 13, 15, 1, 3, 14, 5, 2, 8, 4},
                {3, 15, 0, 6, 10, 1, 13, 8, 9, 4, 5, 11, 12, 7, 2, 14}
        };
        final int[][] S5 = {
                {2, 12, 4, 1, 7, 10, 11, 6, 8, 5, 3, 15, 13, 0, 14, 9},
                {14, 11, 2, 12, 4, 7, 13, 1, 5, 0, 15, 10, 3, 9, 8, 6},
                {4, 2, 1, 11, 10, 13, 7, 8, 15, 9, 12, 5, 6, 3, 0, 14},
                {11, 8, 12, 7, 1, 14, 2, 13, 6, 15, 0, 9, 10, 4, 5, 3}
        };

        final int[][] S6 = {
                {12, 1, 10, 15, 9, 2, 6, 8, 0, 13, 3, 4, 14, 7, 5, 11},
                {10, 15, 4, 2, 7, 12, 9, 5, 6, 1, 13, 14, 0, 11, 3, 8},
                {9, 14, 15, 5, 2, 8, 12, 3, 7, 0, 4, 10, 1, 13, 11, 6},
                {4, 3, 2, 12, 9, 5, 15, 10, 11, 14, 1, 7, 6, 0, 8, 13}
        };

        final int[][] S7 = {
                {4, 11, 2, 14, 15, 0, 8, 13, 3, 12, 9, 7, 5, 10, 6, 1},
                {13, 0, 11, 7, 4, 9, 1, 10, 14, 3, 5, 12, 2, 15, 8, 6},
                {1, 4, 11, 13, 12, 3, 7, 14, 10, 15, 6, 8, 0, 5, 9, 2},
                {6, 11, 13, 8, 1, 4, 10, 7, 9, 5, 0, 15, 14, 2, 3, 12}
        };

        final int[][] S8 = {
                {13, 2, 8, 4, 6, 15, 11, 1, 10, 9, 3, 14, 5, 0, 12, 7},
                {1, 15, 13, 8, 10, 3, 7, 4, 12, 5, 6, 11, 0, 14, 9, 2},
                {7, 11, 4, 1, 9, 12, 14, 2, 0, 6, 10, 13, 15, 3, 5, 8},
                {2, 1, 14, 7, 4, 10, 8, 13, 15, 12, 9, 0, 3, 5, 6, 11}
        };
//замена для каждого байта в  block с использованием sблоков
        //row строка
        //col столбец          10000000                  00000100
        int row = ((block[0] & 0x80) >> 6) | ((block[0] & 0x04) >> 2);
                      //побитовой операция  | дает конечный результат // & выполняет побитовую операцию И чтобы все биты кроме старшего обнунились
                                                                            // по итогу мы  извлекаем самый левый бит
                                                                            // сдвигаем вправо на 6 позиций по итгу значение страшего бита встает на место младшего
                                                                            //получаем двоичное представление числа и объяединяем

        int col = ((block[0] & 0x78) >> 3);//тк одно чило состоит из 4 битов, сдвиг на 3 нужен чтобы отбросить младшие биты
        result[0] = (byte) (S1[row][col] << 4);//заполняем старшие 4 бита

        //S2
        row = ((block[1] & 0x80) >> 6) | ((block[1] & 0x04) >> 2);
        col = ((block[1] & 0x78) >> 3);
        result[0] |= S2[row][col];//заполняем младшие 4 бита

        //S3 Box
        row = ((block[2] & 0x80) >> 6) | ((block[2] & 0x04) >> 2);
        col = ((block[2] & 0x78) >> 3);
        result[1] = (byte) (S3[row][col] << 4);
        //S4
        row = ((block[3] & 0x80) >> 6) | ((block[3] & 0x04) >> 2);
        col = ((block[3] & 0x78) >> 3);
        result[1] |= S4[row][col];
        //S5
        row = ((block[4] & 0x80) >> 6) | ((block[4] & 0x04) >> 2);
        col = ((block[4] & 0x78) >> 3);
        result[2] = (byte) (S5[row][col] << 4);
        //S6
        row = ((block[5] & 0x80) >> 6) | ((block[5] & 0x04) >> 2);
        col = ((block[5] & 0x78) >> 3);
        result[2] |= S6[row][col];
        //S7
        row = ((block[6] & 0x80) >> 6) | ((block[6] & 0x04) >> 2);
        col = ((block[6] & 0x78) >> 3);
        result[3] = (byte) (S7[row][col] << 4);
        //S8
        row = ((block[7] & 0x80) >> 6) | ((block[7] & 0x04) >> 2);
        col = ((block[7] & 0x78) >> 3);
        result[3] |= S8[row][col];

        return result;
    }

    // Перестановка ключа
    private static byte[] permutationKey(byte[] key) {
        byte[] result = new byte[BLOCK_SIZE];// новый массив result который будет содержать результат перестановки ключа
        result[0] = key[7];//байт из исходного ключа с индексом 7 копируется в result с индексом 0
        result[1] = key[3];
        result[2] = key[0];
        result[3] = key[6];
        result[4] = key[4];
        result[5] = key[2];
        result[6] = key[5];
        result[7] = key[1];

        return result;
    }
    // циклический сдвиг влево
    private static byte[] LeftShift(byte[] key, int shift) {
        byte[] result = new byte[BLOCK_SIZE/ 2];//применяем только к половине блока
        for (int i = 0; i < BLOCK_SIZE / 2; i++) {//обработка каждого элемента key[i] половины блока
            result[i] = (byte) (((key[i] << shift) | (key[i] >>> (BLOCK_SIZE / 2 - shift))) & 0xFF);
        }//для сохранения битов которыевыходят за пределы половины блока
        // выполняется операция циклического сдвига вправо элемента на (BLOCK_SIZE / 2 - shift) битов с помощью оператора >>>
        //| для объединения результатов сдвигов
        // проверяем что результат представляет 8битноезначение
        // выполняем & с 0xFF те оставляемт только млдадшие 8 битов

        return result;
    }
    // хор двух блоков
    private static byte[] xor(byte[] block1, byte[] block2) {
        int length = Math.min(block1.length, block2.length);//длина массива- минимальная длина между block1 и block2
        byte[] result = new byte[length];
        for (int i = 0; i < length; i++) {// операция хор побитово для block1[i] и block2[i] с помощью ^
            result[i] = (byte) (block1[i] ^ block2[i]);
        }
        return result;
    }
    public static void main(String[] args) throws FileNotFoundException {
        byte[] key = {0x01, 0x23, 0x45, 0x67, (byte) 0x89, (byte) 0xAB, (byte) 0xCD, (byte) 0xEF}; // 64bit ключ шестнадцетиричные числа
        byte[] iv = {0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, (byte) 0x88}; // 64bit инициализирующий вектор
        System.out.println("Введите a, если хотите самостоятельно ввести текст");
        System.out.println("Введите b, если хотите работать из файла");
        Scanner e = new Scanner(System.in);//создать объект сканера
        String v = e.nextLine();// Получить строку этой строки
        if (v.equals("a")) {
            System.out.println("Введите текст:");
            Scanner d = new Scanner(System.in);// создать объект сканера
            String s0 = d.nextLine();
            System.out.println("Изначальный текст:" + s0);
            byte[] plaintext = s0.getBytes();
            byte[] ciphertext = encrypt(plaintext, key, iv);
            System.out.println("Зашифрованный текст: " + Arrays.toString(ciphertext));
            //деешифрование
            byte[] decryptedText = decrypt(ciphertext, key, iv);
            System.out.println("Расшифрованный текст: " + new String(decryptedText));
        }
            else if (v.equals("b")) {
                String path = "/Users/polinatrehleb/Desktop/polina.txt"; //указываем путь до файла и оформляем его в переменную
                File file = new File(path);//создаем файл чтобы считывать его
                Scanner scanner = new Scanner(file);//передаем сканнеру файл
                String s1 = scanner.nextLine();//считываем строку
                System.out.println("Изначальный текст: " + s1);
                byte[] plaintext2 = s1.getBytes();
                byte[] ciphertext2 = encrypt(plaintext2, key, iv);
                System.out.println("Зашифрованный: " + Arrays.toString(ciphertext2));
                //деешифрование
                byte[] decryptedText2 = decrypt(ciphertext2, key, iv);
                System.out.println("Расшифрованный текст: " + new String(decryptedText2));

            }
        }
    }
