include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cz.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "eluzelz.mm"
include "zmulcl.mm"
include "syl2an.mm"
include "cr.mm"
include "eluz2b1.mm"
include "zre.mm"
include "anim1i.mm"
include "sylbi.mm"
include "mulgt1.mm"
include "an4s.mm"
include "sylanbrc.mm"

theorem uz2mulcl
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ( ZZ>= ` 2 ) /\ N e. ( ZZ>= ` 2 ) ) -> ( M x. N ) e. ( ZZ>= ` 2 ) )

  proof
    cM
    c2
    cuz
    cfv
    #
    wcel
    #
    cN
    @0
    wcel
    #
    wa
    cM
    cN
    cmul
    co
    #
    cz
    wcel
    #
    c1
    @3
    clt
    wbr
    #
    @3
    @0
    wcel
    @1
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @4
    @2
    c2
    cM
    eluzelz
    c2
    cN
    eluzelz
    cM
    cN
    zmulcl
    syl2an
    @1
    cM
    cr
    wcel
    #
    c1
    cM
    clt
    wbr
    #
    wa
    #
    cN
    cr
    wcel
    #
    c1
    cN
    clt
    wbr
    #
    wa
    #
    @5
    @2
    @1
    @6
    @9
    wa
    @10
    cM
    eluz2b1
    @6
    @8
    @9
    cM
    zre
    anim1i
    sylbi
    @2
    @7
    @12
    wa
    @13
    cN
    eluz2b1
    @7
    @11
    @12
    cN
    zre
    anim1i
    sylbi
    @8
    @11
    @9
    @12
    @5
    cM
    cN
    mulgt1
    an4s
    syl2an
    @3
    eluz2b1
    sylanbrc
end
