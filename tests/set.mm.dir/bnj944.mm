include "w-bnj15.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "csuc.mm"
include "wceq.mm"
include "w3a.mm"
include "cvv.mm"
include "wfn.mm"
include "w-bnj17.mm"
include "simpl.mm"
include "bnj667.mm"
include "sylbi.mm"
include "sylibr.mm"
include "3ad2ant1.mm"
include "adantl.mm"
include "bnj1232.mm"
include "vex.mm"
include "bnj216.mm"
include "id.mm"
include "3anim123i.mm"
include "3ancomb.mm"
include "bitri.mm"
include "bnj253.mm"
include "syl3anbrc.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "bnj938.mm"
include "syl5eqel.mm"
include "syl.mm"
include "bnj658.mm"
include "simp3.mm"
include "bnj291.mm"
include "sylanbrc.mm"
include "wi.mm"
include "c0.mm"
include "cif.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "wsbc.mm"
include "opeq2.mm"
include "sneqd.mm"
include "uneq2d.mm"
include "syl5eq.mm"
include "sbceq1d.mm"
include "syl5bb.mm"
include "imbi2d.mm"
include "biid.mm"
include "eqid.mm"
include "0ex.mm"
include "elimel.mm"
include "bnj929.mm"
include "dedth.mm"
include "sylc.mm"

theorem bnj944
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wta: wff ta
  let wsi: wff si
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cX: class X
  let vp: setvar p
  let bnjwphm: wff ph'
  let bnjwphn: wff ph"
  assume bnj944.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj944.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj944.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj944.4: |- ( ph' <-> [. p / n ]. ph )
  assume bnj944.7: |- ( ph" <-> [. G / f ]. ph' )
  assume bnj944.10: |- D = ( _om \ { (/) } )
  assume bnj944.12: |- C = U_ y e. ( f ` m ) _pred ( y , A , R )
  assume bnj944.13: |- G = ( f u. { <. n , C >. } )
  assume bnj944.14: |- ( ta <-> ( f Fn n /\ ph /\ ps ) )
  assume bnj944.15: |- ( si <-> ( n e. D /\ p = suc n /\ m e. n ) )

  disjoint A f
  disjoint A i
  disjoint A m
  disjoint A n
  disjoint f i
  disjoint f m
  disjoint f n
  disjoint i m
  disjoint i n
  disjoint m n
  disjoint A y
  disjoint f y
  disjoint i y
  disjoint m y
  disjoint R f
  disjoint R i
  disjoint R m
  disjoint R n
  disjoint R y
  disjoint X f
  disjoint X n
  assert |- ( ( ( R _FrSe A /\ X e. A ) /\ ( ch /\ n = suc m /\ p = suc n ) ) -> ph" )

  proof
    cA
    cR
    w-bnj15
    #
    cX
    cA
    wcel
    #
    wa
    #
    wch
    vn
    cv
    #
    vm
    cv
    #
    csuc
    wceq
    #
    vp
    cv
    @3
    csuc
    wceq
    #
    w3a
    #
    wa
    #
    cC
    cvv
    wcel
    #
    @3
    cD
    wcel
    #
    @6
    vf
    cv
    #
    @3
    wfn
    #
    wph
    w-bnj17
    #
    bnjwphn
    @8
    @0
    @1
    wta
    wsi
    w-bnj17
    #
    @9
    @8
    @2
    wta
    wsi
    @14
    @2
    @7
    simpl
    @7
    wta
    @2
    wch
    @5
    wta
    @6
    wch
    @12
    wph
    wps
    w3a
    #
    wta
    wch
    @10
    @12
    wph
    wps
    w-bnj17
    #
    @15
    bnj944.3
    @10
    @12
    wph
    wps
    bnj667
    sylbi
    bnj944.14
    sylibr
    3ad2ant1
    adantl
    @7
    wsi
    @2
    @7
    @10
    @4
    @3
    wcel
    #
    @6
    w3a
    #
    wsi
    wch
    @10
    @5
    @17
    @6
    @6
    wch
    @10
    @12
    wph
    wps
    bnj944.3
    bnj1232
    @3
    @4
    vm
    vex
    bnj216
    @6
    id
    3anim123i
    wsi
    @10
    @6
    @17
    w3a
    @18
    bnj944.15
    @10
    @6
    @17
    3ancomb
    bitri
    sylibr
    adantl
    @0
    @1
    wta
    wsi
    bnj253
    syl3anbrc
    @14
    cC
    vy
    @4
    @11
    cfv
    cA
    cR
    vy
    cv
    c-bnj14
    ciun
    cvv
    bnj944.12
    wta
    wsi
    vy
    cA
    cD
    cR
    vf
    vi
    vn
    vp
    cX
    vm
    wph
    wps
    bnj944.10
    bnj944.14
    bnj944.15
    bnj944.1
    bnj944.2
    bnj938
    syl5eqel
    syl
    @7
    @13
    @2
    @7
    @10
    @12
    wph
    w3a
    #
    @6
    @13
    wch
    @5
    @19
    @6
    wch
    @16
    @19
    bnj944.3
    @10
    @12
    wph
    wps
    bnj658
    sylbi
    3ad2ant1
    wch
    @5
    @6
    simp3
    @10
    @6
    @12
    wph
    bnj291
    sylanbrc
    adantl
    @9
    @13
    bnjwphn
    wi
    @13
    bnjwphm
    vf
    @11
    @3
    @9
    cC
    c0
    cif
    #
    cop
    #
    csn
    #
    cun
    #
    wsbc
    #
    wi
    cC
    c0
    cC
    @20
    wceq
    #
    bnjwphn
    @24
    @13
    bnjwphn
    bnjwphm
    vf
    cG
    wsbc
    @25
    @24
    bnj944.7
    @25
    bnjwphm
    vf
    cG
    @23
    @25
    cG
    @11
    @3
    cC
    cop
    #
    csn
    #
    cun
    @23
    bnj944.13
    @25
    @27
    @22
    @11
    @25
    @26
    @21
    cC
    @20
    @3
    opeq2
    sneqd
    uneq2d
    syl5eq
    sbceq1d
    syl5bb
    imbi2d
    wph
    cA
    @20
    cD
    cR
    vf
    vn
    @23
    cX
    vp
    bnjwphm
    @24
    bnj944.1
    bnj944.4
    @24
    biid
    bnj944.10
    @23
    eqid
    cC
    c0
    cvv
    0ex
    elimel
    bnj929
    dedth
    sylc
end
