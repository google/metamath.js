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
include "ccom.mm"
include "psgndif.mm"
include "imp.mm"
include "fveq2d.mm"
include "csymg.mm"
include "cbs.mm"
include "diffi.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "symgfixelsi.mm"
include "adantll.mm"
include "zrhcofipsgn.mm"
include "syl2anc.mm"
include "elrabi.mm"
include "sylan2.mm"
include "adantlr.mm"
include "3eqtr4d.mm"
include "ex.mm"

theorem zrhcopsgndif
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cK: class K
  let cN: class N
  let cY: class Y
  let cZ: class Z
  let vq: setvar q
  assume zrhcopsgndif.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume zrhcopsgndif.s: |- S = ( pmSgn ` N )
  assume zrhcopsgndif.z: |- Z = ( pmSgn ` ( N \ { K } ) )
  assume zrhcopsgndif.y: |- Y = ( ZRHom ` R )

  disjoint K q
  disjoint P q
  disjoint Q q
  assert |- ( ( N e. Fin /\ K e. N ) -> ( Q e. { q e. P | ( q ` K ) = K } -> ( ( Y o. Z ) ` ( Q |` ( N \ { K } ) ) ) = ( ( Y o. S ) ` Q ) ) )

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
    #
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
    cY
    cZ
    ccom
    cfv
    #
    cQ
    cY
    cS
    ccom
    cfv
    #
    wceq
    @2
    @5
    wa
    #
    @8
    cZ
    cfv
    #
    cY
    cfv
    #
    cQ
    cS
    cfv
    #
    cY
    cfv
    #
    @9
    @10
    @11
    @12
    @14
    cY
    @2
    @5
    @12
    @14
    wceq
    cP
    cQ
    cS
    cK
    cN
    cZ
    vq
    zrhcopsgndif.p
    zrhcopsgndif.s
    zrhcopsgndif.z
    psgndif
    imp
    fveq2d
    @11
    @7
    cfn
    wcel
    #
    @8
    @7
    csymg
    cfv
    cbs
    cfv
    #
    wcel
    #
    @9
    @13
    wceq
    @0
    @16
    @1
    @5
    cN
    @6
    diffi
    ad2antrr
    @1
    @5
    @18
    @0
    @7
    cP
    @4
    @17
    cQ
    cK
    cN
    vq
    zrhcopsgndif.p
    @4
    eqid
    @17
    eqid
    #
    @7
    eqid
    symgfixelsi
    adantll
    @17
    @8
    cR
    cZ
    @7
    cY
    @19
    zrhcopsgndif.y
    zrhcopsgndif.z
    zrhcofipsgn
    syl2anc
    @0
    @5
    @10
    @15
    wceq
    #
    @1
    @5
    @0
    cQ
    cP
    wcel
    @20
    @3
    vq
    cQ
    cP
    elrabi
    cP
    cQ
    cR
    cS
    cN
    cY
    zrhcopsgndif.p
    zrhcopsgndif.y
    zrhcopsgndif.s
    zrhcofipsgn
    sylan2
    adantlr
    3eqtr4d
    ex
end
