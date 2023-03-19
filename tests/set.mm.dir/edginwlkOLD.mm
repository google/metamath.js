include "wcel.mm"
include "wfun.mm"
include "cdm.mm"
include "cword.mm"
include "w3a.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wa.mm"
include "crn.mm"
include "simpl2.mm"
include "wrdsymbcl.mm"
include "3ad2antl3.mm"
include "fvelrn.mm"
include "syl2anc.mm"
include "wb.mm"
include "cedg.mm"
include "ciedg.mm"
include "edgvalOLD.mm"
include "eqcomi.mm"
include "rneqi.mm"
include "syl6eq.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "mpbird.mm"
include "ex.mm"

theorem edginwlkOLD
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cK: class K
  let cW: class W
  assume edginwlk.i: |- I = ( iEdg ` G )
  assume edginwlk.e: |- E = ( Edg ` G )


  assert |- ( ( G e. W /\ Fun I /\ F e. Word dom I ) -> ( K e. ( 0 ..^ ( # ` F ) ) -> ( I ` ( F ` K ) ) e. E ) )

  proof
    cG
    cW
    wcel
    #
    cI
    wfun
    #
    cF
    cI
    cdm
    #
    cword
    wcel
    #
    w3a
    #
    cK
    cc0
    cF
    chash
    cfv
    cfzo
    co
    wcel
    #
    cK
    cF
    cfv
    #
    cI
    cfv
    #
    cE
    wcel
    #
    @4
    @5
    wa
    #
    @8
    @7
    cI
    crn
    #
    wcel
    #
    @9
    @1
    @6
    @2
    wcel
    #
    @11
    @0
    @1
    @3
    @5
    simpl2
    @3
    @0
    @5
    @12
    @1
    cK
    @2
    cF
    wrdsymbcl
    3ad2antl3
    @6
    cI
    fvelrn
    syl2anc
    @4
    @8
    @11
    wb
    #
    @5
    @0
    @1
    @13
    @3
    @0
    cE
    @10
    @7
    @0
    cE
    cG
    cedg
    cfv
    #
    @10
    edginwlk.e
    @0
    @14
    cG
    ciedg
    cfv
    #
    crn
    @10
    cG
    cW
    edgvalOLD
    @15
    cI
    cI
    @15
    edginwlk.i
    eqcomi
    rneqi
    syl6eq
    syl5eq
    eleq2d
    3ad2ant1
    adantr
    mpbird
    ex
end
