include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wral.mm"
include "csupp.mm"
include "cc0.mm"
include "cfz.mm"
include "wrex.mm"
include "clt.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "fsuppmapnn0fiubex.mm"
include "wa.mm"
include "wne.mm"
include "crab.mm"
include "wfn.mm"
include "cvv.mm"
include "ssel2.mm"
include "ancoms.mm"
include "elmapfn.mm"
include "syl.mm"
include "expcom.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "imp.mm"
include "nn0ex.mm"
include "a1i.mm"
include "simpll3.mm"
include "suppvalfn.mm"
include "syl3anc.mm"
include "sseq1d.mm"
include "rabss.mm"
include "syl6bb.mm"
include "wn.mm"
include "nne.mm"
include "biimpi.mm"
include "2a1d.mm"
include "cle.mm"
include "elfz2nn0.mm"
include "cr.mm"
include "wb.mm"
include "nn0re.mm"
include "lenlt.mm"
include "syl2an.mm"
include "pm2.21.mm"
include "syl6bi.mm"
include "3impia.mm"
include "a1d.mm"
include "sylbi.mm"
include "ja.mm"
include "com12.mm"
include "ralimdva.mm"
include "sylbid.mm"
include "reximdva.mm"
include "syld.mm"

theorem fsuppmapnn0fiub0
  let vx: setvar x
  let cR: class R
  let vf: setvar f
  let vm: setvar m
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vg: setvar g

  disjoint M f
  disjoint M m
  disjoint f m
  disjoint R f
  disjoint R m
  disjoint V f
  disjoint V m
  disjoint Z f
  disjoint Z m
  disjoint M x
  disjoint R x
  disjoint V x
  disjoint Z x
  disjoint f x
  disjoint m x
  disjoint M g
  disjoint f g
  disjoint g m
  disjoint Z g
  assert |- ( ( M C_ ( R ^m NN0 ) /\ M e. Fin /\ Z e. V ) -> ( A. f e. M f finSupp Z -> E. m e. NN0 A. f e. M A. x e. NN0 ( m < x -> ( f ` x ) = Z ) ) )

  proof
    cM
    cR
    cn0
    cmap
    co
    #
    wss
    #
    cM
    cfn
    wcel
    #
    cZ
    cV
    wcel
    #
    w3a
    #
    vf
    cv
    #
    cZ
    cfsupp
    wbr
    vf
    cM
    wral
    @5
    cZ
    csupp
    co
    #
    cc0
    vm
    cv
    #
    cfz
    co
    #
    wss
    #
    vf
    cM
    wral
    #
    vm
    cn0
    wrex
    @7
    vx
    cv
    #
    clt
    wbr
    #
    @11
    @5
    cfv
    #
    cZ
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    vf
    cM
    wral
    #
    vm
    cn0
    wrex
    cR
    vf
    vm
    cM
    cV
    cZ
    fsuppmapnn0fiubex
    @4
    @10
    @17
    vm
    cn0
    @4
    @7
    cn0
    wcel
    #
    wa
    #
    @9
    @16
    vf
    cM
    @19
    @5
    cM
    wcel
    #
    wa
    #
    @9
    @13
    cZ
    wne
    #
    @11
    @8
    wcel
    #
    wi
    #
    vx
    cn0
    wral
    #
    @16
    @21
    @9
    @22
    vx
    cn0
    crab
    #
    @8
    wss
    @25
    @21
    @6
    @26
    @8
    @21
    @5
    cn0
    wfn
    #
    cn0
    cvv
    wcel
    #
    @3
    @6
    @26
    wceq
    @19
    @20
    @27
    @4
    @20
    @27
    wi
    #
    @18
    @1
    @2
    @29
    @3
    @20
    @1
    @27
    @20
    @1
    wa
    @5
    @0
    wcel
    #
    @27
    @1
    @20
    @30
    cM
    @0
    @5
    ssel2
    ancoms
    @5
    cR
    cn0
    elmapfn
    syl
    expcom
    3ad2ant1
    adantr
    imp
    @28
    @21
    nn0ex
    a1i
    @1
    @2
    @3
    @18
    @20
    simpll3
    vx
    @5
    cvv
    cV
    cn0
    cZ
    suppvalfn
    syl3anc
    sseq1d
    @22
    vx
    cn0
    @8
    rabss
    syl6bb
    @21
    @24
    @15
    vx
    cn0
    @24
    @21
    @11
    cn0
    wcel
    #
    wa
    #
    @15
    @22
    @23
    @32
    @15
    wi
    #
    @22
    wn
    #
    @14
    @32
    @12
    @34
    @14
    @13
    cZ
    nne
    biimpi
    2a1d
    @23
    @31
    @18
    @11
    @7
    cle
    wbr
    #
    w3a
    #
    @33
    @11
    @7
    elfz2nn0
    @36
    @15
    @32
    @31
    @18
    @35
    @15
    @31
    @18
    wa
    @35
    @12
    wn
    #
    @15
    @31
    @11
    cr
    wcel
    @7
    cr
    wcel
    @35
    @37
    wb
    @18
    @11
    nn0re
    @7
    nn0re
    @11
    @7
    lenlt
    syl2an
    @12
    @14
    pm2.21
    syl6bi
    3impia
    a1d
    sylbi
    ja
    com12
    ralimdva
    sylbid
    ralimdva
    reximdva
    syld
end
