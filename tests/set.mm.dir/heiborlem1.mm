include "cfn.mm"
include "wcel.mm"
include "ciun.mm"
include "wss.mm"
include "wrex.mm"
include "wa.mm"
include "wn.mm"
include "cv.mm"
include "cuni.mm"
include "cpw.mm"
include "cin.mm"
include "wral.mm"
include "wceq.mm"
include "sseq1.mm"
include "rexbidv.mm"
include "notbid.mm"
include "elab2.mm"
include "con2bii.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitr2i.mm"
include "wf.mm"
include "cfv.mm"
include "wex.mm"
include "wi.mm"
include "unieq.mm"
include "sseq2d.mm"
include "ac6sfi.mm"
include "ex.mm"
include "adantr.mm"
include "elab2g.mm"
include "ibi.mm"
include "crn.mm"
include "frn.mm"
include "ad2antrl.mm"
include "inss1.mm"
include "syl6ss.mm"
include "sspwuni.mm"
include "sylib.mm"
include "vex.mm"
include "rnex.mm"
include "uniex.mm"
include "elpw.mm"
include "sylibr.mm"
include "wfo.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "fofi.mm"
include "syldan.mm"
include "inss2.mm"
include "unifi.mm"
include "syl2anc.mm"
include "elind.mm"
include "adantlr.mm"
include "simplr.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "adantll.mm"
include "elssuni.mm"
include "uniss.mm"
include "3syl.mm"
include "sstr2.mm"
include "syl5com.mm"
include "ralimdva.mm"
include "impr.mm"
include "iunss.mm"
include "sstrd.mm"
include "rspcev.mm"
include "nsyl3.mm"
include "exlimdv.mm"
include "syld.mm"
include "syl5bi.mm"
include "con4d.mm"
include "3impia.mm"

theorem heiborlem1
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cU: class U
  let cJ: class J
  let cK: class K
  let vn: setvar n
  let vt: setvar t
  let vy: setvar y
  let vk: setvar k
  let vr: setvar r
  let cF: class F
  let vg: setvar g
  let cG: class G
  let wph: wff ph
  let vm: setvar m
  let vz: setvar z
  let cM: class M
  let cT: class T
  let wps: wff ps
  let cS: class S
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume heibor.1: |- J = ( MetOpen ` D )
  assume heibor.3: |- K = { u | -. E. v e. ( ~P U i^i Fin ) u C_ U. v }
  assume heiborlem1.4: |- B e. _V

  disjoint A x
  disjoint u x
  disjoint u v
  disjoint D u
  disjoint v x
  disjoint D v
  disjoint D x
  disjoint B u
  disjoint B v
  disjoint J u
  disjoint J v
  disjoint J x
  disjoint U u
  disjoint U v
  disjoint U x
  disjoint C u
  disjoint C v
  disjoint K x
  disjoint n t
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint x y
  disjoint A y
  disjoint k n
  disjoint k r
  disjoint k t
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint F k
  disjoint n r
  disjoint n u
  disjoint F n
  disjoint r t
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint F r
  disjoint t u
  disjoint F t
  disjoint u y
  disjoint F u
  disjoint F x
  disjoint F y
  disjoint g k
  disjoint g t
  disjoint g x
  disjoint G g
  disjoint G k
  disjoint G t
  disjoint G x
  disjoint g r
  disjoint g ph
  disjoint k ph
  disjoint ph r
  disjoint ph t
  disjoint ph x
  disjoint g m
  disjoint g n
  disjoint g u
  disjoint g v
  disjoint g y
  disjoint g z
  disjoint D g
  disjoint k m
  disjoint k v
  disjoint k z
  disjoint D k
  disjoint m n
  disjoint m r
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint D m
  disjoint n v
  disjoint n z
  disjoint D n
  disjoint r v
  disjoint r z
  disjoint D r
  disjoint t v
  disjoint t z
  disjoint D t
  disjoint u z
  disjoint v y
  disjoint v z
  disjoint x z
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint M g
  disjoint M k
  disjoint M m
  disjoint M r
  disjoint M t
  disjoint M u
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint T m
  disjoint T n
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint B g
  disjoint B n
  disjoint B t
  disjoint B y
  disjoint J g
  disjoint J k
  disjoint J m
  disjoint J n
  disjoint J r
  disjoint J t
  disjoint J y
  disjoint J z
  disjoint U g
  disjoint U n
  disjoint U t
  disjoint U y
  disjoint U z
  disjoint g ps
  disjoint ps t
  disjoint ps y
  disjoint ps z
  disjoint S k
  disjoint S m
  disjoint S n
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint X g
  disjoint X k
  disjoint X m
  disjoint X n
  disjoint X r
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint C m
  disjoint C n
  disjoint C t
  disjoint C y
  disjoint K g
  disjoint K n
  disjoint K t
  disjoint K y
  disjoint K z
  disjoint Y k
  disjoint Y t
  disjoint Y x
  disjoint Z k
  disjoint Z v
  disjoint Z x
  assert |- ( ( A e. Fin /\ C C_ U_ x e. A B /\ C e. K ) -> E. x e. A B e. K )

  proof
    cA
    cfn
    wcel
    #
    cC
    vx
    cA
    cB
    ciun
    #
    wss
    #
    cC
    cK
    wcel
    #
    cB
    cK
    wcel
    #
    vx
    cA
    wrex
    #
    @0
    @2
    wa
    #
    @5
    @3
    @5
    wn
    #
    cB
    vv
    cv
    #
    cuni
    #
    wss
    #
    vv
    cU
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    vx
    cA
    wral
    #
    @6
    @3
    wn
    #
    @14
    @4
    wn
    #
    vx
    cA
    wral
    @7
    @13
    @16
    vx
    cA
    @4
    @13
    vu
    cv
    #
    @9
    wss
    #
    vv
    @12
    wrex
    #
    wn
    #
    @13
    wn
    vu
    cB
    cK
    heiborlem1.4
    @17
    cB
    wceq
    #
    @19
    @13
    @21
    @18
    @10
    vv
    @12
    @17
    cB
    @9
    sseq1
    rexbidv
    notbid
    heibor.3
    elab2
    con2bii
    ralbii
    @4
    vx
    cA
    ralnex
    bitr2i
    @6
    @14
    cA
    @12
    vt
    cv
    #
    wf
    #
    cB
    vx
    cv
    #
    @22
    cfv
    #
    cuni
    #
    wss
    #
    vx
    cA
    wral
    #
    wa
    #
    vt
    wex
    #
    @15
    @0
    @14
    @30
    wi
    @2
    @0
    @14
    @30
    @10
    @27
    vx
    vv
    cA
    @12
    vt
    @8
    @25
    wceq
    @9
    @26
    cB
    @8
    @25
    unieq
    sseq2d
    ac6sfi
    ex
    adantr
    @6
    @29
    @15
    vt
    @6
    @29
    @15
    @3
    cC
    @9
    wss
    #
    vv
    @12
    wrex
    #
    @6
    @29
    wa
    #
    @3
    @32
    wn
    #
    @20
    @34
    vu
    cC
    cK
    cK
    @17
    cC
    wceq
    #
    @19
    @32
    @35
    @18
    @31
    vv
    @12
    @17
    cC
    @9
    sseq1
    rexbidv
    notbid
    heibor.3
    elab2g
    ibi
    @33
    @22
    crn
    #
    cuni
    #
    @12
    wcel
    #
    cC
    @37
    cuni
    #
    wss
    #
    @32
    @0
    @29
    @38
    @2
    @0
    @29
    wa
    #
    @11
    cfn
    @37
    @41
    @37
    cU
    wss
    #
    @37
    @11
    wcel
    @41
    @36
    @11
    wss
    @42
    @41
    @36
    @12
    @11
    @23
    @36
    @12
    wss
    @0
    @28
    cA
    @12
    @22
    frn
    ad2antrl
    #
    @11
    cfn
    inss1
    syl6ss
    @36
    cU
    sspwuni
    sylib
    @37
    cU
    @36
    @22
    vt
    vex
    rnex
    uniex
    elpw
    sylibr
    @41
    @36
    cfn
    wcel
    #
    @36
    cfn
    wss
    @37
    cfn
    wcel
    @0
    @29
    cA
    @36
    @22
    wfo
    #
    @44
    @41
    @22
    cA
    wfn
    #
    @45
    @23
    @46
    @0
    @28
    cA
    @12
    @22
    ffn
    #
    ad2antrl
    cA
    @22
    dffn4
    sylib
    cA
    @36
    @22
    fofi
    syldan
    @41
    @36
    @12
    cfn
    @43
    @11
    cfn
    inss2
    syl6ss
    @36
    unifi
    syl2anc
    elind
    adantlr
    @33
    cC
    @1
    @39
    @0
    @2
    @29
    simplr
    @0
    @29
    @1
    @39
    wss
    #
    @2
    @41
    cB
    @39
    wss
    #
    vx
    cA
    wral
    #
    @48
    @0
    @23
    @28
    @50
    @0
    @23
    wa
    #
    @27
    @49
    vx
    cA
    @51
    @24
    cA
    wcel
    #
    wa
    #
    @26
    @39
    wss
    #
    @27
    @49
    @53
    @25
    @36
    wcel
    #
    @25
    @37
    wss
    @54
    @23
    @52
    @55
    @0
    @23
    @46
    @52
    @55
    @47
    cA
    @24
    @22
    fnfvelrn
    sylan
    adantll
    @25
    @36
    elssuni
    @25
    @37
    uniss
    3syl
    cB
    @26
    @39
    sstr2
    syl5com
    ralimdva
    impr
    vx
    cA
    cB
    @39
    iunss
    sylibr
    adantlr
    sstrd
    @31
    @40
    vv
    @37
    @12
    @8
    @37
    wceq
    @9
    @39
    cC
    @8
    @37
    unieq
    sseq2d
    rspcev
    syl2anc
    nsyl3
    ex
    exlimdv
    syld
    syl5bi
    con4d
    3impia
end
