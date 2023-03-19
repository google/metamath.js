include "cr.mm"
include "wss.mm"
include "cxr.mm"
include "wf.mm"
include "wa.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cin.mm"
include "clt.mm"
include "csup.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "wceq.mm"
include "limsupgval.mm"
include "3ad2ant2.mm"
include "breq1d.mm"
include "wb.mm"
include "inss2.mm"
include "simp3.mm"
include "supxrleub.mm"
include "sylancr.mm"
include "cres.mm"
include "cdm.mm"
include "crn.mm"
include "imassrn.mm"
include "simp1r.mm"
include "frn.mm"
include "syl.mm"
include "syl5ss.mm"
include "df-ss.mm"
include "sylib.mm"
include "imadmres.mm"
include "syl6eqr.mm"
include "raleqdv.mm"
include "wfn.mm"
include "ffn.mm"
include "fdm.mm"
include "ineq2d.mm"
include "dmres.mm"
include "incom.mm"
include "3eqtr4g.mm"
include "inss1.mm"
include "syl6eqss.mm"
include "breq1.mm"
include "ralima.mm"
include "syl2anc.mm"
include "eleq2d.mm"
include "elin.mm"
include "syl6bb.mm"
include "simpl2.mm"
include "simp1l.mm"
include "sselda.mm"
include "elicopnf.mm"
include "baibd.mm"
include "pm5.32da.mm"
include "bitrd.mm"
include "imbi1d.mm"
include "impexp.mm"
include "ralbidv2.mm"
include "3bitrd.mm"

theorem limsupgle
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let cM: class M
  assume limsupval.1: |- G = ( k e. RR |-> sup ( ( ( F " ( k [,) +oo ) ) i^i RR* ) , RR* , < ) )

  disjoint F k
  disjoint A j
  disjoint B j
  disjoint C j
  disjoint C k
  disjoint j k
  disjoint F j
  disjoint k x
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint F x
  disjoint f k
  disjoint G x
  disjoint M k
  disjoint C x
  disjoint j x
  assert |- ( ( ( B C_ RR /\ F : B --> RR* ) /\ C e. RR /\ A e. RR* ) -> ( ( G ` C ) <_ A <-> A. j e. B ( C <_ j -> ( F ` j ) <_ A ) ) )

  proof
    cB
    cr
    wss
    #
    cB
    cxr
    cF
    wf
    #
    wa
    #
    cC
    cr
    wcel
    #
    cA
    cxr
    wcel
    #
    w3a
    #
    cC
    cG
    cfv
    #
    cA
    cle
    wbr
    cF
    cC
    cpnf
    cico
    co
    #
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    csup
    #
    cA
    cle
    wbr
    #
    vx
    cv
    #
    cA
    cle
    wbr
    #
    vx
    @9
    wral
    #
    cC
    vj
    cv
    #
    cle
    wbr
    #
    @15
    cF
    cfv
    #
    cA
    cle
    wbr
    #
    wi
    #
    vj
    cB
    wral
    #
    @5
    @6
    @10
    cA
    cle
    @3
    @2
    @6
    @10
    wceq
    @4
    vk
    cF
    cG
    cC
    limsupval.1
    limsupgval
    3ad2ant2
    breq1d
    @5
    @9
    cxr
    wss
    @4
    @11
    @14
    wb
    @8
    cxr
    inss2
    @2
    @3
    @4
    simp3
    vx
    @9
    cA
    supxrleub
    sylancr
    @5
    @14
    @13
    vx
    cF
    cF
    @7
    cres
    cdm
    #
    cima
    #
    wral
    #
    @18
    vj
    @21
    wral
    #
    @20
    @5
    @13
    vx
    @9
    @22
    @5
    @9
    @8
    @22
    @5
    @8
    cxr
    wss
    @9
    @8
    wceq
    @5
    @8
    cF
    crn
    #
    cxr
    cF
    @7
    imassrn
    @5
    @1
    @25
    cxr
    wss
    @0
    @1
    @3
    @4
    simp1r
    #
    cB
    cxr
    cF
    frn
    syl
    syl5ss
    @8
    cxr
    df-ss
    sylib
    cF
    @7
    imadmres
    syl6eqr
    raleqdv
    @5
    cF
    cB
    wfn
    #
    @21
    cB
    wss
    @23
    @24
    wb
    @5
    @1
    @27
    @26
    cB
    cxr
    cF
    ffn
    syl
    @5
    @21
    cB
    @7
    cin
    #
    cB
    @5
    @7
    cF
    cdm
    #
    cin
    @7
    cB
    cin
    @21
    @28
    @5
    @29
    cB
    @7
    @5
    @1
    @29
    cB
    wceq
    @26
    cB
    cxr
    cF
    fdm
    syl
    ineq2d
    cF
    @7
    dmres
    cB
    @7
    incom
    3eqtr4g
    #
    cB
    @7
    inss1
    syl6eqss
    @13
    @18
    vx
    vj
    cB
    @21
    cF
    @12
    @17
    cA
    cle
    breq1
    ralima
    syl2anc
    @5
    @18
    @19
    vj
    @21
    cB
    @5
    @15
    @21
    wcel
    #
    @18
    wi
    @15
    cB
    wcel
    #
    @16
    wa
    #
    @18
    wi
    @32
    @19
    wi
    @5
    @31
    @33
    @18
    @5
    @31
    @32
    @15
    @7
    wcel
    #
    wa
    #
    @33
    @5
    @31
    @15
    @28
    wcel
    @35
    @5
    @21
    @28
    @15
    @30
    eleq2d
    @15
    cB
    @7
    elin
    syl6bb
    @5
    @32
    @34
    @16
    @5
    @32
    wa
    @3
    @15
    cr
    wcel
    #
    @34
    @16
    wb
    @2
    @3
    @4
    @32
    simpl2
    @5
    cB
    cr
    @15
    @0
    @1
    @3
    @4
    simp1l
    sselda
    @3
    @34
    @36
    @16
    cC
    @15
    elicopnf
    baibd
    syl2anc
    pm5.32da
    bitrd
    imbi1d
    @32
    @16
    @18
    impexp
    syl6bb
    ralbidv2
    3bitrd
    3bitrd
end
