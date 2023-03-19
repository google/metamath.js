include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "wf1o.mm"
include "ccnv.mm"
include "wa.mm"
include "cvsca.mm"
include "cfv.mm"
include "csca.mm"
include "cbs.mm"
include "eqid.mm"
include "clmod.mm"
include "lmhmlmod2.mm"
include "adantr.mm"
include "lmhmlmod1.mm"
include "wceq.mm"
include "lmhmsca.mm"
include "eqcomd.mm"
include "cghm.mm"
include "wb.mm"
include "lmghm.mm"
include "ghmf1o.mm"
include "syl.mm"
include "biimpa.mm"
include "cv.mm"
include "simpll.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "adantrr.mm"
include "wf.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "adantl.mm"
include "ffvelrnda.mm"
include "adantrl.mm"
include "lmhmlin.mm"
include "syl3anc.mm"
include "f1ocnvfv2.mm"
include "ad2ant2l.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "wi.mm"
include "simplr.mm"
include "lmodvscl.mm"
include "f1ocnvfv.mm"
include "syl2anc.mm"
include "mpd.mm"
include "islmhmd.mm"
include "wfn.mm"
include "lmhmf.mm"
include "ffn.mm"
include "dff1o4.mm"
include "sylanbrc.mm"
include "impbida.mm"

theorem lmhmf1o
  let cS: class S
  let cT: class T
  let cF: class F
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  assume lmhmf1o.x: |- X = ( Base ` S )
  assume lmhmf1o.y: |- Y = ( Base ` T )


  assert |- ( F e. ( S LMHom T ) -> ( F : X -1-1-onto-> Y <-> `' F e. ( T LMHom S ) ) )

  proof
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    cX
    cY
    cF
    wf1o
    #
    cF
    ccnv
    #
    cT
    cS
    clmhm
    co
    wcel
    #
    @0
    @1
    wa
    #
    va
    vb
    cT
    cS
    cT
    cvsca
    cfv
    #
    cS
    cvsca
    cfv
    #
    @2
    cS
    csca
    cfv
    #
    cT
    csca
    cfv
    #
    @8
    cbs
    cfv
    #
    cY
    lmhmf1o.y
    @5
    eqid
    #
    @6
    eqid
    #
    @8
    eqid
    #
    @7
    eqid
    #
    @9
    eqid
    @0
    cT
    clmod
    wcel
    @1
    cS
    cT
    cF
    lmhmlmod2
    adantr
    @0
    cS
    clmod
    wcel
    #
    @1
    cS
    cT
    cF
    lmhmlmod1
    adantr
    #
    @0
    @7
    @8
    wceq
    @1
    @0
    @8
    @7
    cS
    cT
    cF
    @7
    @8
    @13
    @12
    lmhmsca
    eqcomd
    adantr
    #
    @0
    @1
    @2
    cT
    cS
    cghm
    co
    wcel
    #
    @0
    cF
    cS
    cT
    cghm
    co
    wcel
    @1
    @17
    wb
    cS
    cT
    cF
    lmghm
    cS
    cT
    cF
    cX
    cY
    lmhmf1o.x
    lmhmf1o.y
    ghmf1o
    syl
    biimpa
    @4
    va
    cv
    #
    @9
    wcel
    #
    vb
    cv
    #
    cY
    wcel
    #
    wa
    #
    wa
    #
    @18
    @20
    @2
    cfv
    #
    @6
    co
    #
    cF
    cfv
    #
    @18
    @20
    @5
    co
    #
    wceq
    #
    @27
    @2
    cfv
    @25
    wceq
    #
    @23
    @26
    @18
    @24
    cF
    cfv
    #
    @5
    co
    #
    @27
    @23
    @0
    @18
    @7
    cbs
    cfv
    #
    wcel
    #
    @24
    cX
    wcel
    #
    @26
    @31
    wceq
    @0
    @1
    @22
    simpll
    @4
    @19
    @33
    @21
    @4
    @33
    @19
    @4
    @32
    @9
    @18
    @4
    @7
    @8
    cbs
    @16
    fveq2d
    eleq2d
    biimpar
    adantrr
    #
    @4
    @21
    @34
    @19
    @4
    cY
    cX
    @20
    @2
    @1
    cY
    cX
    @2
    wf
    #
    @0
    @1
    cY
    cX
    @2
    wf1o
    @36
    cX
    cY
    cF
    f1ocnv
    cY
    cX
    @2
    f1of
    syl
    adantl
    ffvelrnda
    adantrl
    #
    @32
    cS
    cT
    @6
    @5
    cX
    cF
    @7
    @18
    @24
    @13
    @32
    eqid
    #
    lmhmf1o.x
    @11
    @10
    lmhmlin
    syl3anc
    @23
    @30
    @20
    @18
    @5
    @1
    @21
    @30
    @20
    wceq
    @0
    @19
    cX
    cY
    @20
    cF
    f1ocnvfv2
    ad2ant2l
    oveq2d
    eqtrd
    @23
    @1
    @25
    cX
    wcel
    #
    @28
    @29
    wi
    @0
    @1
    @22
    simplr
    @23
    @14
    @33
    @34
    @39
    @4
    @14
    @22
    @15
    adantr
    @35
    @37
    @18
    @6
    @7
    @32
    cX
    cS
    @24
    lmhmf1o.x
    @13
    @11
    @38
    lmodvscl
    syl3anc
    cX
    cY
    @25
    @27
    cF
    f1ocnvfv
    syl2anc
    mpd
    islmhmd
    @0
    @3
    wa
    #
    cF
    cX
    wfn
    #
    @2
    cY
    wfn
    #
    @1
    @0
    @41
    @3
    @0
    cX
    cY
    cF
    wf
    @41
    cX
    cY
    cS
    cT
    cF
    lmhmf1o.x
    lmhmf1o.y
    lmhmf
    cX
    cY
    cF
    ffn
    syl
    adantr
    @40
    @36
    @42
    @3
    @36
    @0
    cY
    cX
    cT
    cS
    @2
    lmhmf1o.y
    lmhmf1o.x
    lmhmf
    adantl
    cY
    cX
    @2
    ffn
    syl
    cX
    cY
    cF
    dff1o4
    sylanbrc
    impbida
end
