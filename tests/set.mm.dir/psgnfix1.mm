include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cgsu.mm"
include "co.mm"
include "cword.mm"
include "wrex.mm"
include "cbs.mm"
include "eqid.mm"
include "csymg.mm"
include "fveq2i.mm"
include "symgfixelsi.mm"
include "adantll.mm"
include "wb.mm"
include "diffi.mm"
include "ad2antrr.mm"
include "psgnfitr.mm"
include "syl.mm"
include "mpbid.mm"
include "ex.mm"

theorem psgnfix1
  let vw: setvar w
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cK: class K
  let cN: class N
  let vq: setvar q
  assume psgnfix.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume psgnfix.t: |- T = ran ( pmTrsp ` ( N \ { K } ) )
  assume psgnfix.s: |- S = ( SymGrp ` ( N \ { K } ) )

  disjoint K q
  disjoint K w
  disjoint N w
  disjoint P q
  disjoint Q w
  disjoint S w
  disjoint T w
  assert |- ( ( N e. Fin /\ K e. N ) -> ( Q e. { q e. P | ( q ` K ) = K } -> E. w e. Word T ( Q |` ( N \ { K } ) ) = ( S gsum w ) ) )

  proof
    cN
    cfn
    wcel
    #
    cK
    cN
    wcel
    #
    wa
    #
    cQ
    cK
    vq
    cv
    cfv
    cK
    wceq
    vq
    cP
    crab
    #
    wcel
    #
    cQ
    cN
    cK
    csn
    #
    cdif
    #
    cres
    #
    cS
    vw
    cv
    cgsu
    co
    wceq
    vw
    cT
    cword
    wrex
    #
    @2
    @4
    wa
    #
    @7
    cS
    cbs
    cfv
    #
    wcel
    #
    @8
    @1
    @4
    @11
    @0
    @6
    cP
    @3
    @10
    cQ
    cK
    cN
    vq
    psgnfix.p
    @3
    eqid
    cS
    @6
    csymg
    cfv
    cbs
    psgnfix.s
    fveq2i
    @6
    eqid
    symgfixelsi
    adantll
    @9
    @6
    cfn
    wcel
    #
    @11
    @8
    wb
    @0
    @12
    @1
    @4
    cN
    @5
    diffi
    ad2antrr
    vw
    @10
    @7
    cT
    cS
    @6
    psgnfix.s
    @10
    eqid
    psgnfix.t
    psgnfitr
    syl
    mpbid
    ex
end
