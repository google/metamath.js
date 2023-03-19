include "cv.mm"
include "wne.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cdif.mm"
include "wcel.mm"
include "eldifad.mm"
include "lcfl1lem.mm"
include "simplbi.mm"
include "syl.mm"
include "lcfl8.mm"
include "mpbid.mm"
include "clsa.mm"
include "fveq2.mm"
include "adantl.mm"
include "chlt.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "dochocsn.mm"
include "eqtrd.mm"
include "sylib.mm"
include "simprd.mm"
include "eldifsni.mm"
include "dvhlmod.mm"
include "lkr0f2.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "eqnetrd.mm"
include "eqid.mm"
include "dochkrsat2.mm"
include "eqeltrrd.mm"
include "clmod.mm"
include "lsatspn0.mm"
include "jca.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "rexdifsn.mm"
include "sylibr.mm"

theorem lcfl8b
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cD: class D
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  assume lcfl8b.h: |- H = ( LHyp ` K )
  assume lcfl8b.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfl8b.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfl8b.v: |- V = ( Base ` U )
  assume lcfl8b.n: |- N = ( LSpan ` U )
  assume lcfl8b.z: |- .0. = ( 0g ` U )
  assume lcfl8b.f: |- F = ( LFnl ` U )
  assume lcfl8b.l: |- L = ( LKer ` U )
  assume lcfl8b.d: |- D = ( LDual ` U )
  assume lcfl8b.y: |- Y = ( 0g ` D )
  assume lcfl8b.c: |- C = { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }
  assume lcfl8b.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfl8b.g: |- ( ph -> G e. ( C \ { Y } ) )

  disjoint C x
  disjoint F f
  disjoint f x
  disjoint G f
  disjoint G x
  disjoint L f
  disjoint L x
  disjoint ._|_ f
  disjoint ._|_ x
  disjoint U x
  disjoint V x
  disjoint ph x
  assert |- ( ph -> E. x e. ( V \ { .0. } ) ( ._|_ ` ( L ` G ) ) = ( N ` { x } ) )

  proof
    wph
    vx
    cv
    #
    c.0
    wne
    #
    cG
    cL
    cfv
    #
    c.pe
    cfv
    #
    @0
    csn
    #
    cN
    cfv
    #
    wceq
    #
    wa
    #
    vx
    cV
    wrex
    #
    @6
    vx
    cV
    c.0
    csn
    cdif
    wrex
    wph
    @2
    @4
    c.pe
    cfv
    #
    wceq
    #
    vx
    cV
    wrex
    #
    @8
    wph
    cG
    cC
    wcel
    #
    @11
    wph
    cG
    cC
    cY
    csn
    #
    lcfl8b.g
    eldifad
    #
    wph
    vx
    cC
    cU
    vf
    cF
    cG
    cH
    cK
    cL
    c.pe
    cV
    cW
    lcfl8b.h
    lcfl8b.o
    lcfl8b.u
    lcfl8b.v
    lcfl8b.f
    lcfl8b.l
    lcfl8b.c
    lcfl8b.k
    wph
    @12
    cG
    cF
    wcel
    #
    @14
    @12
    @15
    @3
    c.pe
    cfv
    #
    @2
    wceq
    #
    cC
    vf
    cF
    cG
    cL
    c.pe
    lcfl8b.c
    lcfl1lem
    #
    simplbi
    syl
    #
    lcfl8
    mpbid
    wph
    @10
    @7
    vx
    cV
    wph
    @0
    cV
    wcel
    #
    wa
    #
    @10
    @7
    @21
    @10
    wa
    #
    @1
    @6
    @22
    @5
    cU
    clsa
    cfv
    #
    wcel
    @1
    @22
    @3
    @5
    @23
    @22
    @3
    @9
    c.pe
    cfv
    #
    @5
    @10
    @3
    @24
    wceq
    @21
    @2
    @9
    c.pe
    fveq2
    adantl
    @22
    cU
    cH
    cK
    cN
    c.pe
    cV
    cW
    @0
    lcfl8b.h
    lcfl8b.u
    lcfl8b.o
    lcfl8b.v
    lcfl8b.n
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @20
    @10
    lcfl8b.k
    ad2antrr
    #
    wph
    @20
    @10
    simplr
    #
    dochocsn
    eqtrd
    #
    @22
    @16
    cV
    wne
    #
    @3
    @23
    wcel
    wph
    @28
    @20
    @10
    wph
    @16
    @2
    cV
    wph
    @15
    @17
    wph
    @12
    @15
    @17
    wa
    @14
    @18
    sylib
    simprd
    wph
    @2
    cV
    wne
    cG
    cY
    wne
    #
    wph
    cG
    cC
    @13
    cdif
    wcel
    @29
    lcfl8b.g
    cG
    cC
    cY
    eldifsni
    syl
    wph
    @2
    cV
    cG
    cY
    wph
    cD
    cF
    cG
    cL
    cV
    cU
    cY
    lcfl8b.v
    lcfl8b.f
    lcfl8b.l
    lcfl8b.d
    lcfl8b.y
    wph
    cU
    cH
    cK
    cW
    lcfl8b.h
    lcfl8b.u
    lcfl8b.k
    dvhlmod
    #
    @19
    lkr0f2
    necon3bid
    mpbird
    eqnetrd
    ad2antrr
    @22
    @23
    cU
    cF
    cG
    cH
    cK
    cL
    c.pe
    cV
    cW
    lcfl8b.h
    lcfl8b.o
    lcfl8b.u
    lcfl8b.v
    @23
    eqid
    #
    lcfl8b.f
    lcfl8b.l
    @25
    wph
    @15
    @20
    @10
    @19
    ad2antrr
    dochkrsat2
    mpbid
    eqeltrrd
    @22
    @23
    cN
    cV
    cU
    @0
    c.0
    lcfl8b.v
    lcfl8b.n
    lcfl8b.z
    @31
    wph
    cU
    clmod
    wcel
    @20
    @10
    @30
    ad2antrr
    @26
    lsatspn0
    mpbid
    @27
    jca
    ex
    reximdva
    mpd
    @6
    vx
    cV
    c.0
    rexdifsn
    sylibr
end
