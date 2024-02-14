
listas_exercises = [
    {
        "name":"lista_infecence",
        "data":  [# Proving inferences
    '0 - p  → q , p ⊢ (q v p)',
    '1 - p → q , ~q ⊢ ~p',
    '2 - p → q , q → s ⊢ p → s',

    ]
    },
        {
        "name":"lista_hypothesis",
        "data": [
    # Proving hypothesis
    '3 - ~~p → q ⊢ p -> q',
    '4 - p → ~~q ⊢ p -> q',
    '5 - p → ~(p ^ r)  ⊢ p →  (~p v ~r)',
    '6 - ~~p ⊢ p',
    '7 - ~p ⊢ ~~~p',
    ]
    },
        {
        "name":"lista_equivalence",
        "data":  [
    # Proving equivalences
    '8 - ~~p → q ⊢ p -> q',
    '9 - p → ~~q ⊢ p -> q',
    '10 - p → ~(p ^ r)  ⊢ p →  (~p v ~r)',
    '11 - ~~p ⊢ p',
    '12 - ~p ⊢ ~~~p',
    ]
    },
        {
        "name":"lista_predicate",
        "data":  [
    # Proving predicates
    '13 - ∼p(a) ⊢ ∼∀xp(x)',
    '14 - ∃x∀y(p(x,y) v q(x,y)) ⊢ p(a,a) v q(a,a)',
    '15 - ∀x(p(x) → q(x)) , ∀x(q(x) → r(x)) ⊢ ∀x(p(x) → r(x))',
    '16 -  ∀x(p(x) ∧ q(x)) ⊢ ∀xp(x) ∧ ∀xq(x)',
    '17 - ~∀xp(x)  ⊢  ∃x~p(x)',
    '18 - ~∃xp(x)  ⊢  ∀x~p(x)',
    '19 - ∀xp(x)  ⊢ ∀xp(x)',
    ],
    },
        {
        "name":"lista_equivalence_02",
        "data":  [
    # Proving equivalences
    '20 - ~~p ⊢ CNF ',
    '21 - p ⊢ DNF ',
    '22 - p ⊢ CNF ',
    '23 - ~p ⊢ CNF '
    #
    ]
    },
]