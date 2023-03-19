include "cabl.mm"
include "cgrp.mm"
include "bj-ablssgrp.mm"
include "sseli.mm"

theorem bj-ablssgrpel
  let cA: class A


  assert |- ( A e. Abel -> A e. Grp )

  proof
    cabl
    cgrp
    cA
    bj-ablssgrp
    sseli
end
