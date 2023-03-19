include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "clsa.mm"
include "clspn.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "adantr.mm"
include "eqid.mm"
include "islsati.mm"
include "sylan.mm"
include "simpr.mm"
include "fveq2d.mm"
include "simp-4r.mm"
include "ad4antr.mm"
include "lcfl1.mm"
include "mpbid.mm"
include "chlt.mm"
include "simplr.mm"
include "snssd.mm"
include "dochocsp.mm"
include "3eqtr3d.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "c0g.mm"
include "lmod0vcl.mm"
include "syl.mm"
include "doch0.mm"
include "eqtr4d.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wo.mm"
include "lcfl3.mm"
include "biimpa.mm"
include "mpjaodan.mm"
include "w3a.mm"
include "cdih.mm"
include "crn.mm"
include "3ad2ant1.mm"
include "wss.mm"
include "simp2.mm"
include "dochcl.mm"
include "dochoc.mm"
include "simp3.mm"
include "3eqtr4d.mm"
include "rexlimdv3a.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem lcfl8
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  assume lcfl8.h: |- H = ( LHyp ` K )
  assume lcfl8.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfl8.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfl8.v: |- V = ( Base ` U )
  assume lcfl8.f: |- F = ( LFnl ` U )
  assume lcfl8.l: |- L = ( LKer ` U )
  assume lcfl8.c: |- C = { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }
  assume lcfl8.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfl8.g: |- ( ph -> G e. F )

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
  assert |- ( ph -> ( G e. C <-> E. x e. V ( L ` G ) = ( ._|_ ` { x } ) ) )

  proof
    wph
    cG
    cC
    wcel
    #
    cG
    cL
    cfv
    #
    vx
    cv
    #
    csn
    #
    c.pe
    cfv
    #
    wceq
    #
    vx
    cV
    wrex
    #
    wph
    @0
    @6
    wph
    @0
    wa
    #
    @1
    c.pe
    cfv
    #
    cU
    clsa
    cfv
    #
    wcel
    #
    @6
    @1
    cV
    wceq
    #
    @7
    @10
    wa
    #
    @8
    @3
    cU
    clspn
    cfv
    #
    cfv
    #
    wceq
    #
    vx
    cV
    wrex
    #
    @6
    @7
    cU
    clmod
    wcel
    #
    @10
    @16
    wph
    @17
    @0
    wph
    cU
    cH
    cK
    cW
    lcfl8.h
    lcfl8.u
    lcfl8.k
    dvhlmod
    adantr
    #
    vx
    @9
    @8
    @13
    cV
    cU
    clmod
    lcfl8.v
    @13
    eqid
    #
    @9
    eqid
    #
    islsati
    sylan
    @12
    @15
    @5
    vx
    cV
    @12
    @2
    cV
    wcel
    #
    wa
    #
    @15
    @5
    @22
    @15
    wa
    #
    @8
    c.pe
    cfv
    #
    @14
    c.pe
    cfv
    @1
    @4
    @23
    @8
    @14
    c.pe
    @22
    @15
    simpr
    fveq2d
    @23
    @0
    @24
    @1
    wceq
    #
    wph
    @0
    @10
    @21
    @15
    simp-4r
    @23
    cC
    vf
    cF
    cG
    cL
    c.pe
    lcfl8.c
    wph
    cG
    cF
    wcel
    @0
    @10
    @21
    @15
    lcfl8.g
    ad4antr
    lcfl1
    mpbid
    @23
    cU
    cH
    cK
    @13
    c.pe
    cV
    cW
    @3
    lcfl8.h
    lcfl8.u
    lcfl8.o
    lcfl8.v
    @19
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @0
    @10
    @21
    @15
    lcfl8.k
    ad4antr
    @23
    @2
    cV
    @12
    @21
    @15
    simplr
    snssd
    dochocsp
    3eqtr3d
    ex
    reximdva
    mpd
    @7
    @11
    wa
    #
    cU
    c0g
    cfv
    #
    cV
    wcel
    #
    @1
    @28
    csn
    #
    c.pe
    cfv
    #
    wceq
    #
    @6
    @27
    @17
    @29
    @7
    @17
    @11
    @18
    adantr
    cV
    cU
    @28
    lcfl8.v
    @28
    eqid
    #
    lmod0vcl
    syl
    @27
    @1
    cV
    @31
    @7
    @11
    simpr
    @27
    @26
    @31
    cV
    wceq
    @7
    @26
    @11
    wph
    @26
    @0
    lcfl8.k
    adantr
    adantr
    cU
    cH
    cK
    c.pe
    cV
    cW
    @28
    lcfl8.h
    lcfl8.u
    lcfl8.o
    lcfl8.v
    @33
    doch0
    syl
    eqtr4d
    @5
    @32
    vx
    @28
    cV
    @2
    @28
    wceq
    #
    @4
    @31
    @1
    @34
    @3
    @30
    c.pe
    @2
    @28
    sneq
    fveq2d
    eqeq2d
    rspcev
    syl2anc
    wph
    @0
    @10
    @11
    wo
    wph
    @9
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
    lcfl8.h
    lcfl8.o
    lcfl8.u
    lcfl8.v
    @20
    lcfl8.f
    lcfl8.l
    lcfl8.c
    lcfl8.k
    lcfl8.g
    lcfl3
    biimpa
    mpjaodan
    ex
    wph
    @6
    @25
    @0
    wph
    @5
    @25
    vx
    cV
    wph
    @21
    @5
    w3a
    #
    @4
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    @4
    @24
    @1
    @35
    @26
    @4
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    wcel
    #
    @37
    @4
    wceq
    wph
    @21
    @26
    @5
    lcfl8.k
    3ad2ant1
    #
    @35
    @26
    @3
    cV
    wss
    @39
    @40
    @35
    @2
    cV
    wph
    @21
    @5
    simp2
    snssd
    cU
    cH
    @38
    cK
    c.pe
    cV
    cW
    @3
    lcfl8.h
    @38
    eqid
    #
    lcfl8.u
    lcfl8.v
    lcfl8.o
    dochcl
    syl2anc
    cH
    @38
    cK
    c.pe
    cW
    @4
    lcfl8.h
    @41
    lcfl8.o
    dochoc
    syl2anc
    @35
    @8
    @36
    c.pe
    @35
    @1
    @4
    c.pe
    wph
    @21
    @5
    simp3
    #
    fveq2d
    fveq2d
    @42
    3eqtr4d
    rexlimdv3a
    wph
    cC
    vf
    cF
    cG
    cL
    c.pe
    lcfl8.c
    lcfl8.g
    lcfl1
    sylibrd
    impbid
end
