include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cmpt.mm"
include "crn.mm"
include "cdm.mm"
include "ccrd.mm"
include "wcel.mm"
include "wfo.mm"
include "wss.mm"
include "con0.mm"
include "word.mm"
include "ordom.mm"
include "cvv.mm"
include "wb.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "elong.mm"
include "syl.mm"
include "mpbiri.mm"
include "ondomen.mm"
include "mpancom.mm"
include "eqid.mm"
include "dmmptss.mm"
include "ssnum.mm"
include "sylancl.mm"
include "wfun.mm"
include "funmpt.mm"
include "funforn.mm"
include "mpbi.mm"
include "fodomnum.mm"
include "mpisyl.mm"
include "brrelexi.mm"
include "ssdomg.mm"
include "domtr.mm"
include "syl2anc.mm"

theorem 1stcrestlem
  let vx: setvar x
  let cB: class B
  let cC: class C
  let va: setvar a
  let vt: setvar t
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cJ: class J
  let cV: class V

  disjoint B x
  disjoint a t
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint J a
  disjoint J t
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint V a
  disjoint V t
  disjoint V w
  disjoint V x
  disjoint V y
  disjoint V z
  assert |- ( B ~<_ _om -> ran ( x e. B |-> C ) ~<_ _om )

  proof
    cB
    com
    cdom
    wbr
    #
    vx
    cB
    cC
    cmpt
    #
    crn
    #
    @1
    cdm
    #
    cdom
    wbr
    #
    @3
    com
    cdom
    wbr
    #
    @2
    com
    cdom
    wbr
    @0
    @3
    ccrd
    cdm
    #
    wcel
    #
    @3
    @2
    @1
    wfo
    #
    @4
    @0
    cB
    @6
    wcel
    #
    @3
    cB
    wss
    #
    @7
    com
    con0
    wcel
    #
    @0
    @9
    @0
    @11
    com
    word
    #
    ordom
    @0
    com
    cvv
    wcel
    @11
    @12
    wb
    cB
    com
    cdom
    reldom
    brrelex2i
    com
    cvv
    elong
    syl
    mpbiri
    com
    cB
    ondomen
    mpancom
    vx
    cB
    cC
    @1
    @1
    eqid
    dmmptss
    #
    cB
    @3
    ssnum
    sylancl
    @1
    wfun
    @8
    vx
    cB
    cC
    funmpt
    @1
    funforn
    mpbi
    @3
    @2
    @1
    fodomnum
    mpisyl
    @3
    cB
    cdom
    wbr
    #
    @0
    @5
    @0
    cB
    cvv
    wcel
    @10
    @14
    cB
    com
    cdom
    reldom
    brrelexi
    @13
    @3
    cB
    cvv
    ssdomg
    mpisyl
    @3
    cB
    com
    domtr
    mpancom
    @2
    @3
    com
    domtr
    syl2anc
end
