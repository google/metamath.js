include "lexicon.mm"
include "we.mm"
include "wM.mm"
include "wU.mm"
include "wI.mm"
include "ax.mm"
include "II.mm"
include "I_.mm"
include "III.mm"
include "IV.mm"

theorem theorem1

  assert |- M U I I U
  proof
    0. we(): wff 
    1. wM(0): wff M
    2. wU(1): wff M U
    3. wI(2): wff M U I
    4. we(): wff 
    5. wI(4): wff I
    6. wU(5): wff I U
    7. we(): wff 
    8. wU(7): wff U
    9. wI(8): wff U I
    10. wU(9): wff U I U
    11. we(): wff 
    12. wM(11): wff M
    13. we(): wff 
    14. wI(13): wff I
    15. wU(14): wff I U
    16. we(): wff 
    17. wM(16): wff M
    18. wI(17): wff M I
    19. wI(18): wff M I I
    20. wI(19): wff M I I I
    21. we(): wff 
    22. wI(21): wff I
    23. wI(22): wff I I
    24. we(): wff 
    25. wI(24): wff I
    26. ax(): |- M I
    27. II(25,26): |- M I I
    28. II(23,27): |- M I I I I
    29. I_(20,28): |- M I I I I U
    30. III(12,15,29): |- M U I U
    31. II(10,30): |- M U I U U I U
    32. IV(3,6,31): |- M U I I U
end
