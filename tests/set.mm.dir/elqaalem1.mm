include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "cz.mm"
include "cn.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eleq1d.mm"
include "rabbidv.mm"
include "infeq1d.mm"
include "ltso.mm"
include "infex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "c1.mm"
include "cuz.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "ssrab2.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "wrex.mm"
include "cq.mm"
include "cply.mm"
include "cc0.mm"
include "wf.mm"
include "c0p.mm"
include "csn.mm"
include "eldifad.mm"
include "0z.mm"
include "zq.mm"
include "ax-mp.mm"
include "coef2.mm"
include "sylancl.mm"
include "ffvelrnda.mm"
include "qmulz.mm"
include "syl.mm"
include "rabn0.mm"
include "sylibr.mm"
include "infssuzcl.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "oveq2.mm"
include "elrab.mm"
include "sylib.mm"

theorem elqaalem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cK: class K
  let cN: class N
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vi: setvar i
  let vj: setvar j
  let cP: class P
  assume elqaa.1: |- ( ph -> A e. CC )
  assume elqaa.2: |- ( ph -> F e. ( ( Poly ` QQ ) \ { 0p } ) )
  assume elqaa.3: |- ( ph -> ( F ` A ) = 0 )
  assume elqaa.4: |- B = ( coeff ` F )
  assume elqaa.5: |- N = ( k e. NN0 |-> inf ( { n e. NN | ( ( B ` k ) x. n ) e. ZZ } , RR , < ) )
  assume elqaa.6: |- R = ( seq 0 ( x. , N ) ` ( deg ` F ) )

  disjoint k n
  disjoint A k
  disjoint A n
  disjoint B k
  disjoint B n
  disjoint k ph
  disjoint K k
  disjoint K n
  disjoint N k
  disjoint N n
  disjoint R k
  disjoint f g
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint k m
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B f
  disjoint B m
  disjoint B z
  disjoint i j
  disjoint P i
  disjoint P j
  disjoint i k
  disjoint i m
  disjoint i z
  disjoint i ph
  disjoint j k
  disjoint j m
  disjoint j z
  disjoint j ph
  disjoint m ph
  disjoint ph z
  disjoint f i
  disjoint f j
  disjoint F f
  disjoint F i
  disjoint F j
  disjoint F m
  disjoint F z
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint K i
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint K j
  disjoint K x
  disjoint K y
  disjoint N i
  disjoint N j
  disjoint N m
  disjoint N x
  disjoint N y
  disjoint R f
  disjoint R m
  disjoint R z
  assert |- ( ( ph /\ K e. NN0 ) -> ( ( N ` K ) e. NN /\ ( ( B ` K ) x. ( N ` K ) ) e. ZZ ) )

  proof
    wph
    cK
    cn0
    wcel
    #
    wa
    #
    cK
    cN
    cfv
    #
    cK
    cB
    cfv
    #
    vn
    cv
    #
    cmul
    co
    #
    cz
    wcel
    #
    vn
    cn
    crab
    #
    wcel
    @2
    cn
    wcel
    @3
    @2
    cmul
    co
    #
    cz
    wcel
    #
    wa
    @1
    @2
    @7
    cr
    clt
    cinf
    #
    @7
    @0
    @2
    @10
    wceq
    wph
    vk
    cK
    vk
    cv
    #
    cB
    cfv
    #
    @4
    cmul
    co
    #
    cz
    wcel
    #
    vn
    cn
    crab
    #
    cr
    clt
    cinf
    @10
    cn0
    cN
    @11
    cK
    wceq
    #
    cr
    @15
    @7
    clt
    @16
    @14
    @6
    vn
    cn
    @16
    @13
    @5
    cz
    @16
    @12
    @3
    @4
    cmul
    @11
    cK
    cB
    fveq2
    oveq1d
    eleq1d
    rabbidv
    infeq1d
    elqaa.5
    cr
    @7
    clt
    ltso
    infex
    fvmpt
    adantl
    @1
    @7
    c1
    cuz
    cfv
    #
    wss
    @7
    c0
    wne
    #
    @10
    @7
    wcel
    @7
    cn
    @17
    @6
    vn
    cn
    ssrab2
    nnuz
    sseqtri
    @1
    @6
    vn
    cn
    wrex
    #
    @18
    @1
    @3
    cq
    wcel
    @19
    wph
    cn0
    cq
    cK
    cB
    wph
    cF
    cq
    cply
    cfv
    #
    wcel
    cc0
    cq
    wcel
    #
    cn0
    cq
    cB
    wf
    wph
    cF
    @20
    c0p
    csn
    elqaa.2
    eldifad
    cc0
    cz
    wcel
    @21
    0z
    cc0
    zq
    ax-mp
    cB
    cq
    cF
    elqaa.4
    coef2
    sylancl
    ffvelrnda
    vn
    @3
    qmulz
    syl
    @6
    vn
    cn
    rabn0
    sylibr
    @7
    c1
    infssuzcl
    sylancr
    eqeltrd
    @6
    @9
    vn
    @2
    cn
    @4
    @2
    wceq
    @5
    @8
    cz
    @4
    @2
    @3
    cmul
    oveq2
    eleq1d
    elrab
    sylib
end
