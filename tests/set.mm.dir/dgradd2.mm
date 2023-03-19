include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "caddc.mm"
include "cof.mm"
include "co.mm"
include "cdgr.mm"
include "wceq.mm"
include "cle.mm"
include "cif.mm"
include "cc.mm"
include "cn0.mm"
include "plyaddcl.mm"
include "3adant3.mm"
include "dgrcl.mm"
include "syl.mm"
include "nn0red.mm"
include "cr.mm"
include "syl5eqel.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "ifcld.mm"
include "dgradd.mm"
include "leidd.mm"
include "simp3.mm"
include "ltled.mm"
include "breq1.mm"
include "ifboth.mm"
include "syl2anc.mm"
include "letrd.mm"
include "ccoe.mm"
include "cc0.mm"
include "wne.mm"
include "eqid.mm"
include "coeadd.mm"
include "fveq1d.mm"
include "cvv.mm"
include "wf.mm"
include "wfn.mm"
include "coef3.mm"
include "ffn.mm"
include "nn0ex.mm"
include "a1i.mm"
include "inidm.mm"
include "wn.mm"
include "ltnled.mm"
include "mpbid.mm"
include "wi.mm"
include "simp1.mm"
include "dgrub.mm"
include "3expia.mm"
include "necon1bd.mm"
include "mpd.mm"
include "adantr.mm"
include "wa.mm"
include "eqidd.mm"
include "ofval.mm"
include "mpdan.mm"
include "ffvelrnd.mm"
include "addid2d.mm"
include "3eqtrd.mm"
include "simp2.mm"
include "0red.mm"
include "nn0ge0d.mm"
include "lelttrd.mm"
include "gt0ne0d.mm"
include "c0p.mm"
include "dgreq0.mm"
include "fveq2.mm"
include "dgr0.mm"
include "eqcomi.mm"
include "3eqtr4g.mm"
include "syl6bir.mm"
include "necon3d.mm"
include "sylc.mm"
include "eqnetrd.mm"
include "syl3anc.mm"
include "letri3d.mm"
include "mpbir2and.mm"

theorem dgradd2
  let cS: class S
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  assume dgradd.1: |- M = ( deg ` F )
  assume dgradd.2: |- N = ( deg ` G )


  assert |- ( ( F e. ( Poly ` S ) /\ G e. ( Poly ` S ) /\ M < N ) -> ( deg ` ( F oF + G ) ) = N )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    cG
    @0
    wcel
    #
    cM
    cN
    clt
    wbr
    #
    w3a
    #
    cF
    cG
    caddc
    cof
    #
    co
    #
    cdgr
    cfv
    #
    cN
    wceq
    @7
    cN
    cle
    wbr
    cN
    @7
    cle
    wbr
    #
    @4
    @7
    cM
    cN
    cle
    wbr
    #
    cN
    cM
    cif
    #
    cN
    @4
    @7
    @4
    @6
    cc
    cply
    cfv
    wcel
    #
    @7
    cn0
    wcel
    @1
    @2
    @11
    @3
    cS
    cF
    cG
    plyaddcl
    3adant3
    #
    cc
    @6
    dgrcl
    syl
    nn0red
    #
    @4
    @9
    cN
    cM
    cr
    @4
    cN
    @2
    @1
    cN
    cn0
    wcel
    #
    @3
    @2
    cN
    cG
    cdgr
    cfv
    #
    cn0
    dgradd.2
    cS
    cG
    dgrcl
    syl5eqel
    3ad2ant2
    #
    nn0red
    #
    @4
    cM
    @1
    @2
    cM
    cn0
    wcel
    @3
    @1
    cM
    cF
    cdgr
    cfv
    cn0
    dgradd.1
    cS
    cF
    dgrcl
    syl5eqel
    3ad2ant1
    #
    nn0red
    #
    ifcld
    @17
    @1
    @2
    @7
    @10
    cle
    wbr
    @3
    cS
    cF
    cG
    cM
    cN
    dgradd.1
    dgradd.2
    dgradd
    3adant3
    @4
    cN
    cN
    cle
    wbr
    #
    @9
    @10
    cN
    cle
    wbr
    #
    @4
    cN
    @17
    leidd
    @4
    cM
    cN
    @19
    @17
    @1
    @2
    @3
    simp3
    #
    ltled
    @9
    @20
    @9
    @21
    cN
    cM
    cN
    @10
    cN
    cle
    breq1
    cM
    @10
    cN
    cle
    breq1
    ifboth
    syl2anc
    letrd
    @4
    @11
    @14
    cN
    @6
    ccoe
    cfv
    #
    cfv
    #
    cc0
    wne
    @8
    @12
    @16
    @4
    @24
    cN
    cG
    ccoe
    cfv
    #
    cfv
    #
    cc0
    @4
    @24
    cN
    cF
    ccoe
    cfv
    #
    @25
    @5
    co
    #
    cfv
    #
    cc0
    @26
    caddc
    co
    #
    @26
    @4
    cN
    @23
    @28
    @1
    @2
    @23
    @28
    wceq
    @3
    @27
    @25
    cS
    cF
    cG
    @27
    eqid
    #
    @25
    eqid
    #
    coeadd
    3adant3
    fveq1d
    @4
    @14
    @29
    @30
    wceq
    @16
    @4
    cn0
    cn0
    cc0
    @26
    caddc
    cn0
    @27
    @25
    cvv
    cvv
    cN
    @4
    cn0
    cc
    @27
    wf
    #
    @27
    cn0
    wfn
    @1
    @2
    @33
    @3
    @27
    cS
    cF
    @31
    coef3
    3ad2ant1
    cn0
    cc
    @27
    ffn
    syl
    @4
    cn0
    cc
    @25
    wf
    #
    @25
    cn0
    wfn
    @2
    @1
    @34
    @3
    @25
    cS
    cG
    @32
    coef3
    3ad2ant2
    #
    cn0
    cc
    @25
    ffn
    syl
    cn0
    cvv
    wcel
    @4
    nn0ex
    a1i
    #
    @36
    cn0
    inidm
    @4
    cN
    @27
    cfv
    #
    cc0
    wceq
    #
    @14
    @4
    cN
    cM
    cle
    wbr
    #
    wn
    #
    @38
    @4
    @3
    @40
    @22
    @4
    cM
    cN
    @19
    @17
    ltnled
    mpbid
    @4
    @39
    @37
    cc0
    @4
    @1
    @14
    @37
    cc0
    wne
    #
    @39
    wi
    @1
    @2
    @3
    simp1
    @16
    @1
    @14
    @41
    @39
    @27
    cS
    cF
    cN
    cM
    @31
    dgradd.1
    dgrub
    3expia
    syl2anc
    necon1bd
    mpd
    adantr
    @4
    @14
    wa
    @26
    eqidd
    ofval
    mpdan
    @4
    @26
    @4
    cn0
    cc
    cN
    @25
    @35
    @16
    ffvelrnd
    addid2d
    3eqtrd
    @4
    @2
    cN
    cc0
    wne
    @26
    cc0
    wne
    @1
    @2
    @3
    simp2
    @4
    cN
    @4
    cc0
    cM
    cN
    @4
    0red
    @19
    @17
    @4
    cM
    @18
    nn0ge0d
    @22
    lelttrd
    gt0ne0d
    @2
    @26
    cc0
    cN
    cc0
    @2
    @26
    cc0
    wceq
    cG
    c0p
    wceq
    #
    cN
    cc0
    wceq
    @25
    cS
    cG
    cN
    dgradd.2
    @32
    dgreq0
    @42
    @15
    c0p
    cdgr
    cfv
    #
    cN
    cc0
    cG
    c0p
    cdgr
    fveq2
    dgradd.2
    @43
    cc0
    dgr0
    eqcomi
    3eqtr4g
    syl6bir
    necon3d
    sylc
    eqnetrd
    @23
    cc
    @6
    cN
    @7
    @23
    eqid
    @7
    eqid
    dgrub
    syl3anc
    @4
    @7
    cN
    @13
    @17
    letri3d
    mpbir2and
end
