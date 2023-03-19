include "cn.mm"
include "cle.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wcel.mm"
include "wral.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cc.mm"
include "absf.mm"
include "subf.mm"
include "fco.mm"
include "mp2an.mm"
include "wss.mm"
include "inss2.mm"
include "ax-resscn.mm"
include "xpss12.mm"
include "sstri.mm"
include "fss.mm"
include "mpan2.mm"
include "sylancr.mm"
include "feq1i.mm"
include "sylibr.mm"
include "ffn.mm"
include "syl.mm"
include "wa.mm"
include "wbr.mm"
include "ffvelrnda.mm"
include "c2nd.mm"
include "c1st.mm"
include "w3a.mm"
include "ovolfcl.mm"
include "wb.mm"
include "subge0.mm"
include "ancoms.mm"
include "biimp3ar.mm"
include "ovolfsval.mm"
include "breqtrrd.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "ralrimiva.mm"
include "ffnfv.mm"

theorem ovolfsf
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  assume ovolfs.1: |- G = ( ( abs o. - ) o. F )


  assert |- ( F : NN --> ( <_ i^i ( RR X. RR ) ) -> G : NN --> ( 0 [,) +oo ) )

  proof
    cn
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cF
    wf
    #
    cG
    cn
    wfn
    #
    vx
    cv
    #
    cG
    cfv
    #
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    vx
    cn
    wral
    cn
    @6
    cG
    wf
    @2
    cn
    cr
    cG
    wf
    #
    @3
    @2
    cn
    cr
    cabs
    cmin
    ccom
    #
    cF
    ccom
    #
    wf
    #
    @8
    @2
    cc
    cc
    cxp
    #
    cr
    @9
    wf
    #
    cn
    @12
    cF
    wf
    #
    @11
    cc
    cr
    cabs
    wf
    @12
    cc
    cmin
    wf
    @13
    absf
    subf
    @12
    cc
    cr
    cabs
    cmin
    fco
    mp2an
    @2
    @1
    @12
    wss
    @14
    @1
    @0
    @12
    cle
    @0
    inss2
    cr
    cc
    wss
    #
    @15
    @0
    @12
    wss
    ax-resscn
    ax-resscn
    cr
    cc
    cr
    cc
    xpss12
    mp2an
    sstri
    cn
    @1
    @12
    cF
    fss
    mpan2
    cn
    @12
    cr
    @9
    cF
    fco
    sylancr
    cn
    cr
    cG
    @10
    ovolfs.1
    feq1i
    sylibr
    #
    cn
    cr
    cG
    ffn
    syl
    @2
    @7
    vx
    cn
    @2
    @4
    cn
    wcel
    wa
    #
    @5
    cr
    wcel
    cc0
    @5
    cle
    wbr
    @7
    @2
    cn
    cr
    @4
    cG
    @16
    ffvelrnda
    @17
    cc0
    @4
    cF
    cfv
    #
    c2nd
    cfv
    #
    @18
    c1st
    cfv
    #
    cmin
    co
    #
    @5
    cle
    @17
    @20
    cr
    wcel
    #
    @19
    cr
    wcel
    #
    @20
    @19
    cle
    wbr
    #
    w3a
    cc0
    @21
    cle
    wbr
    #
    cF
    @4
    ovolfcl
    @22
    @23
    @25
    @24
    @23
    @22
    @25
    @24
    wb
    @19
    @20
    subge0
    ancoms
    biimp3ar
    syl
    cF
    cG
    @4
    ovolfs.1
    ovolfsval
    breqtrrd
    @5
    elrege0
    sylanbrc
    ralrimiva
    vx
    cn
    @6
    cG
    ffnfv
    sylanbrc
end
