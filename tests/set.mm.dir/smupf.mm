include "cn0.mm"
include "cpw.mm"
include "cv.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "wa.mm"
include "crab.mm"
include "csad.mm"
include "cmpt2.mm"
include "cc0.mm"
include "wceq.mm"
include "c0.mm"
include "c1.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "wf.mm"
include "cvv.mm"
include "cfv.mm"
include "0nn0.mm"
include "iftrue.mm"
include "eqid.mm"
include "0ex.mm"
include "fvmpt.mm"
include "mp1i.mm"
include "0elpw.mm"
include "syl6eqel.mm"
include "cop.mm"
include "df-ov.mm"
include "cxp.mm"
include "wral.mm"
include "wss.mm"
include "elpwi.mm"
include "adantr.mm"
include "ssrab2.mm"
include "sadcl.mm"
include "sylancl.mm"
include "nn0ex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "rgen2.mm"
include "fmpt2.mm"
include "mpbi.mm"
include "f0cli.mm"
include "eqeltri.mm"
include "a1i.mm"
include "nn0uz.mm"
include "0zd.mm"
include "caddc.mm"
include "cuz.mm"
include "fvexd.mm"
include "seqf2.mm"
include "feq1i.mm"

theorem smupf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  let cM: class M
  assume smuval.a: |- ( ph -> A C_ NN0 )
  assume smuval.b: |- ( ph -> B C_ NN0 )
  assume smuval.p: |- P = seq 0 ( ( p e. ~P NN0 , m e. NN0 |-> ( p sadd { n e. NN0 | ( m e. A /\ ( n - m ) e. B ) } ) ) , ( n e. NN0 |-> if ( n = 0 , (/) , ( n - 1 ) ) ) )

  disjoint m n
  disjoint m p
  disjoint A m
  disjoint n p
  disjoint A n
  disjoint A p
  disjoint n ph
  disjoint B m
  disjoint B n
  disjoint B p
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m x
  disjoint m y
  disjoint n x
  disjoint n y
  disjoint p x
  disjoint p y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint N k
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint M k
  disjoint M x
  disjoint P k
  disjoint P x
  disjoint P y
  assert |- ( ph -> P : NN0 --> ~P NN0 )

  proof
    wph
    cn0
    cn0
    cpw
    #
    vp
    vm
    @0
    cn0
    vp
    cv
    #
    vm
    cv
    #
    cA
    wcel
    vn
    cv
    #
    @2
    cmin
    co
    cB
    wcel
    wa
    #
    vn
    cn0
    crab
    #
    csad
    co
    #
    cmpt2
    #
    vn
    cn0
    @3
    cc0
    wceq
    #
    c0
    @3
    c1
    cmin
    co
    #
    cif
    #
    cmpt
    #
    cc0
    cseq
    #
    wf
    cn0
    @0
    cP
    wf
    wph
    vx
    vy
    @0
    cvv
    @7
    @11
    cc0
    cn0
    wph
    cc0
    @11
    cfv
    #
    c0
    @0
    cc0
    cn0
    wcel
    @13
    c0
    wceq
    wph
    0nn0
    vn
    cc0
    @10
    c0
    cn0
    @11
    @8
    c0
    @9
    iftrue
    @11
    eqid
    0ex
    fvmpt
    mp1i
    cn0
    0elpw
    #
    syl6eqel
    vx
    cv
    #
    vy
    cv
    #
    @7
    co
    #
    @0
    wcel
    wph
    @15
    @0
    wcel
    @16
    cvv
    wcel
    wa
    wa
    @17
    @15
    @16
    cop
    #
    @7
    cfv
    @0
    @15
    @16
    @7
    df-ov
    @0
    cn0
    cxp
    #
    @0
    @18
    @7
    @6
    @0
    wcel
    #
    vm
    cn0
    wral
    vp
    @0
    wral
    @19
    @0
    @7
    wf
    @20
    vp
    vm
    @0
    cn0
    @1
    @0
    wcel
    #
    @2
    cn0
    wcel
    #
    wa
    #
    @6
    cn0
    wss
    #
    @20
    @23
    @1
    cn0
    wss
    #
    @5
    cn0
    wss
    @24
    @21
    @25
    @22
    @1
    cn0
    elpwi
    adantr
    @4
    vn
    cn0
    ssrab2
    @1
    @5
    sadcl
    sylancl
    @6
    cn0
    nn0ex
    elpw2
    sylibr
    rgen2
    vp
    vm
    @0
    cn0
    @6
    @0
    @7
    @7
    eqid
    fmpt2
    mpbi
    @14
    f0cli
    eqeltri
    a1i
    nn0uz
    wph
    0zd
    wph
    @15
    cc0
    c1
    caddc
    co
    cuz
    cfv
    wcel
    wa
    @15
    @11
    fvexd
    seqf2
    cn0
    @0
    cP
    @12
    smuval.p
    feq1i
    sylibr
end
