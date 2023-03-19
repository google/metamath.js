include "cv.mm"
include "co.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "cfn.mm"
include "oveq1.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "nfcv.mm"
include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "com.mm"
include "crab.mm"
include "cint.mm"
include "cif.mm"
include "cmpt2.mm"
include "nfmpt21.mm"
include "nfcxfr.mm"
include "nfov.mm"
include "nfeq1.mm"
include "nfmpt22.mm"
include "weq.mm"
include "vex.mm"
include "fvex.mm"
include "ifex.mm"
include "ovmpt4g.mm"
include "mp3an.mm"
include "iftrue.mm"
include "syl5eq.mm"
include "adantr.mm"
include "vtocl2gaf.mm"
include "vtocl2ga.mm"

theorem pwfseqlem2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cD: class D
  let cR: class R
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vy: setvar y
  let va: setvar a
  let vb: setvar b
  let vs: setvar s
  let vv: setvar v
  let cW: class W
  let cZ: class Z
  assume pwfseqlem4.g: |- ( ph -> G : ~P A -1-1-> U_ n e. _om ( A ^m n ) )
  assume pwfseqlem4.x: |- ( ph -> X C_ A )
  assume pwfseqlem4.h: |- ( ph -> H : _om -1-1-onto-> X )
  assume pwfseqlem4.ps: |- ( ps <-> ( ( x C_ A /\ r C_ ( x X. x ) /\ r We x ) /\ _om ~<_ x ) )
  assume pwfseqlem4.k: |- ( ( ph /\ ps ) -> K : U_ n e. _om ( x ^m n ) -1-1-> x )
  assume pwfseqlem4.d: |- D = ( G ` { w e. x | ( ( `' K ` w ) e. ran G /\ -. w e. ( `' G ` ( `' K ` w ) ) ) } )
  assume pwfseqlem4.f: |- F = ( x e. _V , r e. _V |-> if ( x e. Fin , ( H ` ( card ` x ) ) , ( D ` |^| { z e. _om | -. ( D ` z ) e. x } ) ) )

  disjoint n r
  disjoint n w
  disjoint n x
  disjoint n z
  disjoint r w
  disjoint r x
  disjoint r z
  disjoint w x
  disjoint w z
  disjoint x z
  disjoint D n
  disjoint D z
  disjoint G w
  disjoint K w
  disjoint H r
  disjoint H x
  disjoint H z
  disjoint n ph
  disjoint ph r
  disjoint ph x
  disjoint ph z
  disjoint n ps
  disjoint ps z
  disjoint A n
  disjoint A r
  disjoint A x
  disjoint A z
  disjoint V r
  disjoint V x
  disjoint n y
  disjoint y z
  disjoint D y
  disjoint a b
  disjoint a s
  disjoint a v
  disjoint a y
  disjoint F a
  disjoint b s
  disjoint b v
  disjoint b y
  disjoint F b
  disjoint s v
  disjoint s y
  disjoint F s
  disjoint v y
  disjoint F v
  disjoint F y
  disjoint w y
  disjoint G y
  disjoint K y
  disjoint a r
  disjoint a x
  disjoint a z
  disjoint H a
  disjoint b r
  disjoint b x
  disjoint b z
  disjoint H b
  disjoint r s
  disjoint r v
  disjoint r y
  disjoint s x
  disjoint s z
  disjoint H s
  disjoint v x
  disjoint v z
  disjoint H v
  disjoint x y
  disjoint H y
  disjoint a n
  disjoint a ph
  disjoint b n
  disjoint b ph
  disjoint n s
  disjoint n v
  disjoint ph s
  disjoint ph v
  disjoint R s
  disjoint A a
  disjoint A s
  disjoint A y
  disjoint W a
  disjoint W b
  disjoint W s
  disjoint W v
  disjoint Z a
  disjoint Z b
  disjoint Z s
  disjoint Z v
  disjoint Y a
  disjoint Y s
  disjoint V a
  disjoint V s
  assert |- ( ( Y e. Fin /\ R e. V ) -> ( Y F R ) = ( H ` ( card ` Y ) ) )

  proof
    va
    cv
    #
    vs
    cv
    #
    cF
    co
    #
    @0
    ccrd
    cfv
    #
    cH
    cfv
    #
    wceq
    #
    cY
    @1
    cF
    co
    #
    cY
    ccrd
    cfv
    #
    cH
    cfv
    #
    wceq
    cY
    cR
    cF
    co
    #
    @8
    wceq
    va
    vs
    cY
    cR
    cfn
    cV
    @0
    cY
    wceq
    #
    @2
    @6
    @4
    @8
    @0
    cY
    @1
    cF
    oveq1
    @10
    @3
    @7
    cH
    @0
    cY
    ccrd
    fveq2
    fveq2d
    eqeq12d
    @1
    cR
    wceq
    @6
    @9
    @8
    @1
    cR
    cY
    cF
    oveq2
    eqeq1d
    vx
    cv
    #
    vr
    cv
    #
    cF
    co
    #
    @11
    ccrd
    cfv
    #
    cH
    cfv
    #
    wceq
    #
    @0
    @12
    cF
    co
    #
    @4
    wceq
    @5
    vx
    vr
    @0
    @1
    cfn
    cV
    vx
    @0
    nfcv
    #
    vr
    @0
    nfcv
    #
    vr
    @1
    nfcv
    #
    vx
    @17
    @4
    vx
    @0
    @12
    cF
    @18
    vx
    cF
    vx
    vr
    cvv
    cvv
    @11
    cfn
    wcel
    #
    @15
    vz
    cv
    cD
    cfv
    @11
    wcel
    wn
    vz
    com
    crab
    cint
    #
    cD
    cfv
    #
    cif
    #
    cmpt2
    #
    pwfseqlem4.f
    vx
    vr
    cvv
    cvv
    @24
    nfmpt21
    nfcxfr
    vx
    @12
    nfcv
    nfov
    nfeq1
    vr
    @2
    @4
    vr
    @0
    @1
    cF
    @19
    vr
    cF
    @25
    pwfseqlem4.f
    vx
    vr
    cvv
    cvv
    @24
    nfmpt22
    nfcxfr
    @20
    nfov
    nfeq1
    vx
    va
    weq
    #
    @13
    @17
    @15
    @4
    @11
    @0
    @12
    cF
    oveq1
    @26
    @14
    @3
    cH
    @11
    @0
    ccrd
    fveq2
    fveq2d
    eqeq12d
    vr
    vs
    weq
    @17
    @2
    @4
    @12
    @1
    @0
    cF
    oveq2
    eqeq1d
    @21
    @16
    @12
    cV
    wcel
    @21
    @13
    @24
    @15
    @11
    cvv
    wcel
    @12
    cvv
    wcel
    @24
    cvv
    wcel
    @13
    @24
    wceq
    vx
    vex
    vr
    vex
    @21
    @15
    @23
    @14
    cH
    fvex
    @22
    cD
    fvex
    ifex
    vx
    vr
    cvv
    cvv
    @24
    cF
    cvv
    pwfseqlem4.f
    ovmpt4g
    mp3an
    @21
    @15
    @23
    iftrue
    syl5eq
    adantr
    vtocl2gaf
    vtocl2ga
end
