include "cun.mm"
include "cfv.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "undif1.mm"
include "fveq2i.mm"
include "cmeas.mm"
include "wcel.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "measbase.mm"
include "syl.mm"
include "difelsiga.mm"
include "syl3anc.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtr3i.mm"
include "a1i.mm"
include "measun.mm"
include "syl121anc.mm"
include "syl5eqr.mm"
include "cxr.mm"
include "wbr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "iccssxr.mm"
include "measvxrge0.mm"
include "syl2anc.mm"
include "sseldi.mm"
include "wa.mm"
include "inelsiga.mm"
include "elxrge0.mm"
include "sylib.mm"
include "simprd.mm"
include "wi.mm"
include "xraddge02.mm"
include "mpd.mm"
include "uncom.mm"
include "inundif.mm"
include "inindif.mm"
include "breqtrrd.mm"
include "xleadd1a.mm"
include "syl31anc.mm"
include "eqbrtrd.mm"

theorem measunl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cM: class M
  assume measunl.1: |- ( ph -> M e. ( measures ` S ) )
  assume measunl.2: |- ( ph -> A e. S )
  assume measunl.3: |- ( ph -> B e. S )


  assert |- ( ph -> ( M ` ( A u. B ) ) <_ ( ( M ` A ) +e ( M ` B ) ) )

  proof
    wph
    cA
    cB
    cun
    #
    cM
    cfv
    #
    cA
    cB
    cdif
    #
    cM
    cfv
    #
    cB
    cM
    cfv
    #
    cxad
    co
    #
    cA
    cM
    cfv
    #
    @4
    cxad
    co
    #
    cle
    wph
    @1
    @2
    cB
    cun
    #
    cM
    cfv
    #
    @5
    @8
    @0
    cM
    cA
    cB
    undif1
    fveq2i
    wph
    cM
    cS
    cmeas
    cfv
    wcel
    #
    @2
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    @2
    cB
    cin
    #
    c0
    wceq
    #
    @9
    @5
    wceq
    measunl.1
    wph
    cS
    csiga
    crn
    cuni
    wcel
    #
    cA
    cS
    wcel
    #
    @12
    @11
    wph
    @10
    @15
    measunl.1
    cS
    cM
    measbase
    syl
    #
    measunl.2
    measunl.3
    cA
    cB
    cS
    difelsiga
    syl3anc
    #
    measunl.3
    @14
    wph
    cB
    @2
    cin
    @13
    c0
    cB
    @2
    incom
    cB
    cA
    disjdif
    eqtr3i
    a1i
    @2
    cB
    cS
    cM
    measun
    syl121anc
    syl5eqr
    wph
    @3
    cxr
    wcel
    #
    @6
    cxr
    wcel
    @4
    cxr
    wcel
    @3
    @6
    cle
    wbr
    @5
    @7
    cle
    wbr
    wph
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @3
    cc0
    cpnf
    iccssxr
    #
    wph
    @10
    @11
    @3
    @20
    wcel
    measunl.1
    @18
    @2
    cS
    cM
    measvxrge0
    syl2anc
    sseldi
    #
    wph
    @20
    cxr
    @6
    @21
    wph
    @10
    @16
    @6
    @20
    wcel
    measunl.1
    measunl.2
    cA
    cS
    cM
    measvxrge0
    syl2anc
    sseldi
    wph
    @20
    cxr
    @4
    @21
    wph
    @10
    @12
    @4
    @20
    wcel
    measunl.1
    measunl.3
    cB
    cS
    cM
    measvxrge0
    syl2anc
    sseldi
    wph
    @3
    @3
    cA
    cB
    cin
    #
    cM
    cfv
    #
    cxad
    co
    #
    @6
    cle
    wph
    cc0
    @24
    cle
    wbr
    #
    @3
    @25
    cle
    wbr
    #
    wph
    @24
    cxr
    wcel
    #
    @26
    wph
    @24
    @20
    wcel
    #
    @28
    @26
    wa
    wph
    @10
    @23
    cS
    wcel
    #
    @29
    measunl.1
    wph
    @15
    @16
    @12
    @30
    @17
    measunl.2
    measunl.3
    cA
    cB
    cS
    inelsiga
    syl3anc
    #
    @23
    cS
    cM
    measvxrge0
    syl2anc
    #
    @24
    elxrge0
    sylib
    simprd
    wph
    @19
    @28
    @26
    @27
    wi
    @22
    wph
    @20
    cxr
    @24
    @21
    @32
    sseldi
    @3
    @24
    xraddge02
    syl2anc
    mpd
    wph
    @6
    @2
    @23
    cun
    #
    cM
    cfv
    #
    @25
    @33
    cA
    cM
    @23
    @2
    cun
    @33
    cA
    @23
    @2
    uncom
    cA
    cB
    inundif
    eqtr3i
    fveq2i
    wph
    @10
    @11
    @30
    @2
    @23
    cin
    #
    c0
    wceq
    #
    @34
    @25
    wceq
    measunl.1
    @18
    @31
    @36
    wph
    @23
    @2
    cin
    @35
    c0
    @23
    @2
    incom
    cA
    cB
    inindif
    eqtr3i
    a1i
    @2
    @23
    cS
    cM
    measun
    syl121anc
    syl5eqr
    breqtrrd
    @3
    @6
    @4
    xleadd1a
    syl31anc
    eqbrtrd
end
