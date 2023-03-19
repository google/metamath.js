include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "id.mm"
include "halfre.mm"
include "a1i.mm"
include "readdcld.mm"
include "flle.mm"
include "syl.mm"
include "reflcl.mm"
include "lesubaddd.mm"
include "mpbird.mm"
include "wa.mm"
include "jca.mm"
include "resubcl.mm"
include "subge0d.mm"

theorem dnibndlem4
  let cB: class B


  assert |- ( B e. RR -> 0 <_ ( B - ( ( |_ ` ( B + ( 1 / 2 ) ) ) - ( 1 / 2 ) ) ) )

  proof
    cB
    cr
    wcel
    #
    cc0
    cB
    cB
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cfl
    cfv
    #
    @1
    cmin
    co
    #
    cmin
    co
    cle
    wbr
    @4
    cB
    cle
    wbr
    #
    @0
    @5
    @3
    @2
    cle
    wbr
    #
    @0
    @2
    cr
    wcel
    #
    @6
    @0
    cB
    @1
    @0
    id
    #
    @1
    cr
    wcel
    #
    @0
    halfre
    a1i
    #
    readdcld
    #
    @2
    flle
    syl
    @0
    @3
    @1
    cB
    @0
    @7
    @3
    cr
    wcel
    #
    @11
    @2
    reflcl
    syl
    #
    @10
    @8
    lesubaddd
    mpbird
    @0
    cB
    @4
    @8
    @0
    @12
    @9
    wa
    @4
    cr
    wcel
    @0
    @12
    @9
    @13
    @10
    jca
    @3
    @1
    resubcl
    syl
    subge0d
    mpbird
end
