include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wa.mm"
include "cfn.mm"
include "cpr.mm"
include "wss.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "cfv.mm"
include "crn.mm"
include "cfz.mm"
include "fzfi.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cle.mm"
include "w3a.mm"
include "simpl.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "elfz1b.mm"
include "sylib.mm"
include "simp2d.mm"
include "nnred.mm"
include "1red.mm"
include "readdcld.mm"
include "lep1d.mm"
include "simp3d.mm"
include "letrd.mm"
include "3jca.mm"
include "sylibr.mm"
include "syl6eleqr.mm"
include "prssi.mm"
include "syl2anc.mm"
include "wne.mm"
include "ltp1d.mm"
include "ltned.mm"
include "pr2nelem.mm"
include "syl3anc.mm"
include "eqid.mm"
include "pmtrrn.mm"

theorem pmtrto1cl
  let cD: class D
  let cT: class T
  let cK: class K
  let cN: class N
  assume psgnfzto1st.d: |- D = ( 1 ... N )
  assume pmtrto1cl.t: |- T = ( pmTrsp ` D )


  assert |- ( ( K e. NN /\ ( K + 1 ) e. D ) -> ( T ` { K , ( K + 1 ) } ) e. ran T )

  proof
    cK
    cn
    wcel
    #
    cK
    c1
    caddc
    co
    #
    cD
    wcel
    #
    wa
    #
    cD
    cfn
    wcel
    #
    cK
    @1
    cpr
    #
    cD
    wss
    #
    @5
    c2o
    cen
    wbr
    #
    @5
    cT
    cfv
    cT
    crn
    #
    wcel
    @4
    @3
    cD
    c1
    cN
    cfz
    co
    #
    cfn
    psgnfzto1st.d
    c1
    cN
    fzfi
    eqeltri
    a1i
    @3
    cK
    cD
    wcel
    #
    @2
    @6
    @3
    cK
    @9
    cD
    @3
    @0
    cN
    cn
    wcel
    #
    cK
    cN
    cle
    wbr
    #
    w3a
    cK
    @9
    wcel
    @3
    @0
    @11
    @12
    @0
    @2
    simpl
    #
    @3
    @1
    cn
    wcel
    #
    @11
    @1
    cN
    cle
    wbr
    #
    @3
    @1
    @9
    wcel
    @14
    @11
    @15
    w3a
    @3
    @1
    cD
    @9
    @0
    @2
    simpr
    #
    psgnfzto1st.d
    syl6eleq
    cN
    @1
    elfz1b
    sylib
    #
    simp2d
    #
    @3
    cK
    @1
    cN
    @3
    cK
    @13
    nnred
    #
    @3
    cK
    c1
    @19
    @3
    1red
    readdcld
    @3
    cN
    @18
    nnred
    @3
    cK
    @19
    lep1d
    @3
    @14
    @11
    @15
    @17
    simp3d
    letrd
    3jca
    cN
    cK
    elfz1b
    sylibr
    psgnfzto1st.d
    syl6eleqr
    #
    @16
    cK
    @1
    cD
    prssi
    syl2anc
    @3
    @10
    @2
    cK
    @1
    wne
    @7
    @20
    @16
    @3
    cK
    @1
    @19
    @3
    cK
    @19
    ltp1d
    ltned
    cK
    @1
    cD
    cD
    pr2nelem
    syl3anc
    cD
    @5
    @8
    cT
    cfn
    pmtrto1cl.t
    @8
    eqid
    pmtrrn
    syl3anc
end
