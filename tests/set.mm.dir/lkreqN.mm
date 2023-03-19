include "cfv.mm"
include "wceq.mm"
include "c0g.mm"
include "wne.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "co.mm"
include "eqeq1d.mm"
include "csca.mm"
include "cbs.mm"
include "eqid.mm"
include "lduallvec.mm"
include "csn.mm"
include "eldifad.mm"
include "clvec.mm"
include "ldualsbase.mm"
include "eleqtrrd.mm"
include "ldualelvbase.mm"
include "lvecvs0or.mm"
include "wcel.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "ldual0.mm"
include "eqeq2d.mm"
include "cdif.mm"
include "eldifsni.mm"
include "a1d.mm"
include "necon4d.mm"
include "sylbid.mm"
include "idd.mm"
include "jaod.mm"
include "nne.mm"
include "syl6ibr.mm"
include "con3d.mm"
include "orrd.mm"
include "ianor.mm"
include "sylibr.mm"
include "wss.mm"
include "wpss.mm"
include "df-pss.mm"
include "ldualvscl.mm"
include "eqeltrd.mm"
include "lkrpssN.mm"
include "syl5rbbr.mm"
include "lkrss.mm"
include "fveq2d.mm"
include "sseqtr4d.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "necon2bbid.mm"
include "mpbird.mm"
include "eqcomd.mm"

theorem lkreqN
  let wph: wff ph
  let cA: class A
  let cD: class D
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let c.0: class .0.
  assume lkreq.s: |- S = ( Scalar ` W )
  assume lkreq.r: |- R = ( Base ` S )
  assume lkreq.o: |- .0. = ( 0g ` S )
  assume lkreq.f: |- F = ( LFnl ` W )
  assume lkreq.k: |- K = ( LKer ` W )
  assume lkreq.d: |- D = ( LDual ` W )
  assume lkreq.t: |- .x. = ( .s ` D )
  assume lkreq.w: |- ( ph -> W e. LVec )
  assume lkreq.a: |- ( ph -> A e. ( R \ { .0. } ) )
  assume lkreq.h: |- ( ph -> H e. F )
  assume lkreq.g: |- ( ph -> G = ( A .x. H ) )


  assert |- ( ph -> ( K ` G ) = ( K ` H ) )

  proof
    wph
    cH
    cK
    cfv
    #
    cG
    cK
    cfv
    #
    wph
    @0
    @1
    wceq
    cH
    cD
    c0g
    cfv
    #
    wne
    #
    cG
    @2
    wceq
    #
    wa
    #
    wn
    #
    wph
    @3
    wn
    #
    @4
    wn
    #
    wo
    @6
    wph
    @7
    @8
    wph
    @4
    @7
    wph
    @4
    cH
    @2
    wceq
    #
    @7
    wph
    @4
    cA
    cH
    c.x
    co
    #
    @2
    wceq
    #
    @9
    wph
    cG
    @10
    @2
    lkreq.g
    eqeq1d
    wph
    @11
    cA
    cD
    csca
    cfv
    #
    c0g
    cfv
    #
    wceq
    #
    @9
    wo
    @9
    wph
    cA
    c.x
    @12
    @12
    cbs
    cfv
    #
    @13
    cD
    cbs
    cfv
    #
    cD
    cH
    @2
    @16
    eqid
    #
    lkreq.t
    @12
    eqid
    #
    @15
    eqid
    #
    @13
    eqid
    #
    @2
    eqid
    #
    wph
    cD
    cW
    lkreq.d
    lkreq.w
    lduallvec
    wph
    cA
    cR
    @15
    wph
    cA
    cR
    c.0
    csn
    #
    lkreq.a
    eldifad
    #
    wph
    cD
    @12
    cS
    @15
    cR
    clvec
    cW
    lkreq.s
    lkreq.r
    lkreq.d
    @18
    @19
    lkreq.w
    ldualsbase
    eleqtrrd
    wph
    cD
    cF
    cH
    @16
    cW
    clvec
    lkreq.f
    lkreq.d
    @17
    lkreq.w
    lkreq.h
    ldualelvbase
    lvecvs0or
    wph
    @14
    @9
    @9
    wph
    @14
    cA
    c.0
    wceq
    @9
    wph
    @13
    c.0
    cA
    wph
    cD
    cS
    @12
    @13
    cW
    c.0
    lkreq.s
    lkreq.o
    lkreq.d
    @18
    @20
    wph
    cW
    clvec
    wcel
    cW
    clmod
    wcel
    lkreq.w
    cW
    lveclmod
    syl
    #
    ldual0
    eqeq2d
    wph
    cH
    @2
    cA
    c.0
    wph
    cA
    c.0
    wne
    #
    @3
    wph
    cA
    cR
    @22
    cdif
    wcel
    @25
    lkreq.a
    cA
    cR
    c.0
    eldifsni
    syl
    a1d
    necon4d
    sylbid
    wph
    @9
    idd
    jaod
    sylbid
    sylbid
    cH
    @2
    nne
    syl6ibr
    con3d
    orrd
    @3
    @4
    ianor
    sylibr
    wph
    @5
    @0
    @1
    wph
    @5
    @0
    @1
    wss
    #
    @0
    @1
    wne
    #
    wa
    #
    @27
    @28
    @0
    @1
    wpss
    wph
    @5
    @0
    @1
    df-pss
    wph
    cD
    cF
    cH
    cG
    cK
    cW
    @2
    lkreq.f
    lkreq.k
    lkreq.d
    @21
    lkreq.w
    lkreq.h
    wph
    cG
    @10
    cF
    lkreq.g
    wph
    cD
    cS
    c.x
    cF
    cH
    cR
    cW
    cA
    lkreq.f
    lkreq.s
    lkreq.r
    lkreq.d
    lkreq.t
    @24
    @23
    lkreq.h
    ldualvscl
    eqeltrd
    lkrpssN
    syl5rbbr
    wph
    @26
    @27
    wph
    @0
    @10
    cK
    cfv
    @1
    wph
    cD
    cS
    c.x
    cF
    cH
    cR
    cK
    cW
    cA
    lkreq.s
    lkreq.r
    lkreq.f
    lkreq.k
    lkreq.d
    lkreq.t
    lkreq.w
    lkreq.h
    @23
    lkrss
    wph
    cG
    @10
    cK
    lkreq.g
    fveq2d
    sseqtr4d
    biantrurd
    bitr4d
    necon2bbid
    mpbird
    eqcomd
end
