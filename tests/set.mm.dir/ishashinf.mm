include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cpw.mm"
include "wrex.mm"
include "cn.mm"
include "wa.mm"
include "wex.mm"
include "wss.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "ccrd.mm"
include "cen.mm"
include "wbr.mm"
include "com.mm"
include "wral.mm"
include "fzfid.mm"
include "ficardom.mm"
include "syl.mm"
include "isinf.mm"
include "breq2.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "rspcva.mm"
include "syl2anr.mm"
include "wi.mm"
include "selpw.mm"
include "biimpri.mm"
include "a1i.mm"
include "hasheni.mm"
include "adantl.mm"
include "hashcard.mm"
include "cn0.mm"
include "nnnn0.mm"
include "hashfz1.mm"
include "eqtrd.mm"
include "ad2antlr.mm"
include "ex.mm"
include "anim12d.mm"
include "eximdv.mm"
include "mpd.mm"
include "df-rex.mm"
include "sylibr.mm"
include "ralrimiva.mm"

theorem ishashinf
  let vx: setvar x
  let cA: class A
  let vn: setvar n
  let va: setvar a

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint a n
  disjoint a x
  disjoint A a
  assert |- ( -. A e. Fin -> A. n e. NN E. x e. ~P A ( # ` x ) = n )

  proof
    cA
    cfn
    wcel
    wn
    #
    vx
    cv
    #
    chash
    cfv
    #
    vn
    cv
    #
    wceq
    #
    vx
    cA
    cpw
    #
    wrex
    #
    vn
    cn
    @0
    @3
    cn
    wcel
    #
    wa
    #
    @1
    @5
    wcel
    #
    @4
    wa
    #
    vx
    wex
    #
    @6
    @8
    @1
    cA
    wss
    #
    @1
    c1
    @3
    cfz
    co
    #
    ccrd
    cfv
    #
    cen
    wbr
    #
    wa
    #
    vx
    wex
    #
    @11
    @7
    @14
    com
    wcel
    #
    @12
    @1
    va
    cv
    #
    cen
    wbr
    #
    wa
    #
    vx
    wex
    #
    va
    com
    wral
    @17
    @0
    @7
    @13
    cfn
    wcel
    #
    @18
    @7
    c1
    @3
    fzfid
    #
    @13
    ficardom
    syl
    vx
    cA
    va
    isinf
    @22
    @17
    va
    @14
    com
    @19
    @14
    wceq
    #
    @21
    @16
    vx
    @25
    @20
    @15
    @12
    @19
    @14
    @1
    cen
    breq2
    anbi2d
    exbidv
    rspcva
    syl2anr
    @8
    @16
    @10
    vx
    @8
    @12
    @9
    @15
    @4
    @12
    @9
    wi
    @8
    @9
    @12
    vx
    cA
    selpw
    biimpri
    a1i
    @8
    @15
    @4
    @8
    @15
    wa
    @2
    @14
    chash
    cfv
    #
    @3
    @15
    @2
    @26
    wceq
    @8
    @1
    @14
    hasheni
    adantl
    @7
    @26
    @3
    wceq
    @0
    @15
    @7
    @26
    @13
    chash
    cfv
    #
    @3
    @7
    @23
    @26
    @27
    wceq
    @24
    @13
    hashcard
    syl
    @7
    @3
    cn0
    wcel
    @27
    @3
    wceq
    @3
    nnnn0
    @3
    hashfz1
    syl
    eqtrd
    ad2antlr
    eqtrd
    ex
    anim12d
    eximdv
    mpd
    @4
    vx
    @5
    df-rex
    sylibr
    ralrimiva
end
