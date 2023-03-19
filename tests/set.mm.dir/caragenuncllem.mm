include "cun.mm"
include "cin.mm"
include "cfv.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "ssinss1d.mm"
include "caragensplit.mm"
include "eqcomd.mm"
include "wceq.mm"
include "inass.mm"
include "incom.mm"
include "inabs.mm"
include "eqtri.mm"
include "ineq2i.mm"
include "fveq2i.mm"
include "indifcom.mm"
include "eqtr2i.mm"
include "eqcomi.mm"
include "c0.mm"
include "difundir.mm"
include "difid.mm"
include "uneq1i.mm"
include "0un.mm"
include "3eqtrri.mm"
include "indif2.mm"
include "oveq12i.mm"
include "a1i.mm"
include "eqidd.mm"
include "3eqtrd.mm"
include "difun1.mm"
include "oveq12d.mm"
include "cxr.mm"
include "wcel.mm"
include "cmnf.mm"
include "wne.mm"
include "wa.mm"
include "omexrcl.mm"
include "omecl.mm"
include "xrge0nemnfd.mm"
include "jca.mm"
include "caragenelss.mm"
include "ssinss2d.mm"
include "ssdifssd.mm"
include "xaddass.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem caragenuncllem
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cE: class E
  let cF: class F
  let cO: class O
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume caragenuncllem.o: |- ( ph -> O e. OutMeas )
  assume caragenuncllem.s: |- S = ( CaraGen ` O )
  assume caragenuncllem.e: |- ( ph -> E e. S )
  assume caragenuncllem.f: |- ( ph -> F e. S )
  assume caragenuncllem.x: |- X = U. dom O
  assume caragenuncllem.a: |- ( ph -> A C_ X )


  assert |- ( ph -> ( ( O ` ( A i^i ( E u. F ) ) ) +e ( O ` ( A \ ( E u. F ) ) ) ) = ( O ` A ) )

  proof
    wph
    cA
    cE
    cF
    cun
    #
    cin
    #
    cO
    cfv
    #
    cA
    @0
    cdif
    #
    cO
    cfv
    #
    cxad
    co
    cA
    cE
    cin
    #
    cO
    cfv
    #
    cA
    cE
    cdif
    #
    cF
    cin
    #
    cO
    cfv
    #
    cxad
    co
    #
    @7
    cF
    cdif
    #
    cO
    cfv
    #
    cxad
    co
    #
    @6
    @9
    @12
    cxad
    co
    #
    cxad
    co
    #
    cA
    cO
    cfv
    #
    wph
    @2
    @10
    @4
    @12
    cxad
    wph
    @2
    @1
    cE
    cin
    #
    cO
    cfv
    #
    @1
    cE
    cdif
    #
    cO
    cfv
    #
    cxad
    co
    #
    @10
    @10
    wph
    @21
    @2
    wph
    @1
    cS
    cE
    cO
    cX
    caragenuncllem.o
    caragenuncllem.s
    caragenuncllem.x
    caragenuncllem.e
    wph
    cA
    @0
    cX
    caragenuncllem.a
    ssinss1d
    caragensplit
    eqcomd
    @21
    @10
    wceq
    wph
    @18
    @6
    @20
    @9
    cxad
    @17
    @5
    cO
    @17
    cA
    @0
    cE
    cin
    #
    cin
    @5
    cA
    @0
    cE
    inass
    @22
    cE
    cA
    @22
    cE
    @0
    cin
    cE
    @0
    cE
    incom
    cE
    cF
    inabs
    eqtri
    ineq2i
    eqtri
    fveq2i
    @19
    @8
    cO
    @8
    cA
    cF
    cE
    cdif
    #
    cin
    #
    cA
    @0
    cE
    cdif
    #
    cin
    @19
    @24
    @8
    @8
    cF
    @7
    cin
    @24
    @7
    cF
    incom
    cF
    cA
    cE
    indifcom
    eqtr2i
    eqcomi
    @23
    @25
    cA
    @25
    cE
    cE
    cdif
    #
    @23
    cun
    c0
    @23
    cun
    @23
    cE
    cF
    cE
    difundir
    @26
    c0
    @23
    cE
    difid
    uneq1i
    @23
    0un
    3eqtrri
    ineq2i
    cA
    @0
    cE
    indif2
    3eqtrri
    fveq2i
    oveq12i
    a1i
    wph
    @10
    eqidd
    3eqtrd
    @4
    @12
    wceq
    wph
    @3
    @11
    cO
    cA
    cE
    cF
    difun1
    fveq2i
    a1i
    oveq12d
    wph
    @6
    cxr
    wcel
    #
    @6
    cmnf
    wne
    #
    wa
    @9
    cxr
    wcel
    #
    @9
    cmnf
    wne
    #
    wa
    @12
    cxr
    wcel
    #
    @12
    cmnf
    wne
    #
    wa
    @13
    @15
    wceq
    wph
    @27
    @28
    wph
    @5
    cO
    cX
    caragenuncllem.o
    caragenuncllem.x
    wph
    cA
    cE
    cX
    caragenuncllem.a
    ssinss1d
    #
    omexrcl
    wph
    @6
    wph
    @5
    cO
    cX
    caragenuncllem.o
    caragenuncllem.x
    @33
    omecl
    xrge0nemnfd
    jca
    wph
    @29
    @30
    wph
    @8
    cO
    cX
    caragenuncllem.o
    caragenuncllem.x
    wph
    @7
    cF
    cX
    wph
    cF
    cS
    cO
    cX
    caragenuncllem.o
    caragenuncllem.s
    caragenuncllem.f
    caragenuncllem.x
    caragenelss
    ssinss2d
    #
    omexrcl
    wph
    @9
    wph
    @8
    cO
    cX
    caragenuncllem.o
    caragenuncllem.x
    @34
    omecl
    xrge0nemnfd
    jca
    wph
    @31
    @32
    wph
    @11
    cO
    cX
    caragenuncllem.o
    caragenuncllem.x
    wph
    @7
    cX
    cF
    wph
    cA
    cX
    cE
    caragenuncllem.a
    ssdifssd
    #
    ssdifssd
    #
    omexrcl
    wph
    @12
    wph
    @11
    cO
    cX
    caragenuncllem.o
    caragenuncllem.x
    @36
    omecl
    xrge0nemnfd
    jca
    @6
    @9
    @12
    xaddass
    syl3anc
    wph
    @15
    @6
    @7
    cO
    cfv
    #
    cxad
    co
    @16
    wph
    @14
    @37
    @6
    cxad
    wph
    @7
    cS
    cF
    cO
    cX
    caragenuncllem.o
    caragenuncllem.s
    caragenuncllem.x
    caragenuncllem.f
    @35
    caragensplit
    oveq2d
    wph
    cA
    cS
    cE
    cO
    cX
    caragenuncllem.o
    caragenuncllem.s
    caragenuncllem.x
    caragenuncllem.e
    caragenuncllem.a
    caragensplit
    eqtrd
    3eqtrd
end
