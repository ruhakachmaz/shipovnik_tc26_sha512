# Shipovnik

[Шиповник](https://kryptonite.ru/articles/how-eds-will-change-in-the-post-quantum-era/) - квантово-устойчивый алгоритм электронно-цифровой подписи, реализуемый с использованием операций над кодами, исправляющими ошибки, определенными над конечным простым полем из двух элементов.

Данный репозиторий содержит открытую реализацию этого алгоритма на языке Си от компании [QApp](https://qapp.tech) разработанную совместно с авторами алгоритма компанией [Криптонит](https://kryptonite.ru/) в сотрудничестве в рамках [ТК26](https://tc26.ru/).

# Сборка проекта

Для сборки требуется `cmake` версии `3.12` или более новой. Поддерживаются следующие опции:

- `GOST_OPTIMIZATION`. С помощью этой опции можно задать уровень оптимизации хэша `GOST 34.11-2012`, используемого в алгоритме. Различные уровни оптимизаций могут поддерживаться не на всех платформах.
  - `0` нет оптимизации
  - `1` инструкции MMX
  - `2` инструкции SSE2
  - `3` инструкции SSE4.1
- `ENTROPY_SOURCE` задает источник энтропии для генерации ключевых пар и подписей. Значение по умолчанию - `/dev/urandom`. Для генерации тестов с известным ответом (`KAT`) можно задать путь к файлу с детерминированными данными, например `/dev/zero`.

Пример сборки проекта:

```bash
$ mkdir build
$ cd build
$ cmake -DGOST_OPTIMIZATION=1 -DENTROPY_SOURCE=/dev/zero ..
$ make
```

# Использование проекта

Проект компилируется в библиотеку, которую можно использовать в сторонних решениях. Для этого нужно либо добавить исходные тексты командой `add_subdirectory(shipovnik)`, либо установить библиотеку командой `make install` и затем выполнить `find_package(shipovnik)`.

## KAT

Программа `shipovnik_example` генерирует данные для тестов с известным ответом (Known Answer Test, `KAT`) при использовании детерминированного источника энтропии (см. раздел "сборка проекта"). По умолчанию она генерирует случайные данные.
