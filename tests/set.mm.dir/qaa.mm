include "cq.mm"
include "wcel.mm"
include "cc.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cply.mm"
include "c0p.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "caa.mm"
include "qcn.mm"
include "cidp.mm"
include "cxp.mm"
include "cmin.mm"
include "cof.mm"
include "co.mm"
include "wne.mm"
include "wss.mm"
include "c1.mm"
include "qsscn.mm"
include "cz.mm"
include "1z.mm"
include "zq.mm"
include "ax-mp.mm"
include "plyid.mm"
include "mp2an.mm"
include "a1i.mm"
include "plyconst.mm"
include "mpan.mm"
include "wa.mm"
include "caddc.mm"
include "qaddcl.mm"
include "adantl.mm"
include "cmul.mm"
include "qmulcl.mm"
include "cneg.mm"
include "qnegcl.mm"
include "plysub.mm"
include "peano2cn.mm"
include "syl.mm"
include "cvv.mm"
include "wfn.mm"
include "cid.mm"
include "cres.mm"
include "fnresi.mm"
include "df-idp.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "fnconstg.mm"
include "cnex.mm"
include "inidm.mm"
include "fveq1i.mm"
include "fvresi.mm"
include "syl5eq.mm"
include "fvconst2g.mm"
include "ofval.mm"
include "mpdan.mm"
include "ax-1cn.mm"
include "pncan2.mm"
include "sylancl.mm"
include "eqtrd.mm"
include "ax-1ne0.mm"
include "eqnetrd.mm"
include "ne0p.mm"
include "syl2anc.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "subidd.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "elqaa.mm"

theorem qaa
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  let cP: class P
  let wph: wff ph
  let cF: class F
  let cK: class K
  let cN: class N
  let cR: class R


  assert |- ( A e. QQ -> A e. AA )

  proof
    cA
    cq
    wcel
    #
    cA
    cc
    wcel
    #
    cA
    vf
    cv
    #
    cfv
    #
    cc0
    wceq
    #
    vf
    cq
    cply
    cfv
    #
    c0p
    csn
    cdif
    #
    wrex
    #
    cA
    caa
    wcel
    cA
    qcn
    #
    @0
    cidp
    cc
    cA
    csn
    cxp
    #
    cmin
    cof
    co
    #
    @6
    wcel
    #
    cA
    @10
    cfv
    #
    cc0
    wceq
    #
    @7
    @0
    @10
    @5
    wcel
    @10
    c0p
    wne
    #
    @11
    @0
    vx
    vy
    cq
    cidp
    @9
    cidp
    @5
    wcel
    #
    @0
    cq
    cc
    wss
    #
    c1
    cq
    wcel
    #
    @15
    qsscn
    c1
    cz
    wcel
    @17
    1z
    c1
    zq
    ax-mp
    #
    cq
    plyid
    mp2an
    a1i
    @16
    @0
    @9
    @5
    wcel
    qsscn
    cA
    cq
    plyconst
    mpan
    vx
    cv
    #
    cq
    wcel
    vy
    cv
    #
    cq
    wcel
    wa
    #
    @19
    @20
    caddc
    co
    cq
    wcel
    @0
    @19
    @20
    qaddcl
    adantl
    @21
    @19
    @20
    cmul
    co
    cq
    wcel
    @0
    @19
    @20
    qmulcl
    adantl
    c1
    cneg
    cq
    wcel
    #
    @0
    @17
    @22
    @18
    c1
    qnegcl
    ax-mp
    a1i
    plysub
    @0
    cA
    c1
    caddc
    co
    #
    cc
    wcel
    #
    @23
    @10
    cfv
    #
    cc0
    wne
    @14
    @0
    @1
    @24
    @8
    cA
    peano2cn
    syl
    #
    @0
    @25
    c1
    cc0
    @0
    @25
    @23
    cA
    cmin
    co
    #
    c1
    @0
    @24
    @25
    @27
    wceq
    @26
    @0
    cc
    cc
    @23
    cA
    cmin
    cc
    cidp
    @9
    cvv
    cvv
    @23
    cidp
    cc
    wfn
    #
    @0
    @28
    cid
    cc
    cres
    #
    cc
    wfn
    cc
    fnresi
    cc
    cidp
    @29
    df-idp
    fneq1i
    mpbir
    a1i
    #
    cc
    cA
    cq
    fnconstg
    #
    cc
    cvv
    wcel
    @0
    cnex
    a1i
    #
    @32
    cc
    inidm
    #
    @24
    @23
    cidp
    cfv
    #
    @23
    wceq
    @0
    @24
    @34
    @23
    @29
    cfv
    @23
    @23
    cidp
    @29
    df-idp
    fveq1i
    cc
    @23
    fvresi
    syl5eq
    adantl
    cc
    cA
    @23
    cq
    fvconst2g
    ofval
    mpdan
    @0
    @1
    c1
    cc
    wcel
    @27
    c1
    wceq
    @8
    ax-1cn
    cA
    c1
    pncan2
    sylancl
    eqtrd
    c1
    cc0
    wne
    @0
    ax-1ne0
    a1i
    eqnetrd
    @23
    @10
    ne0p
    syl2anc
    @10
    @5
    c0p
    eldifsn
    sylanbrc
    @0
    @12
    cA
    cA
    cmin
    co
    #
    cc0
    @0
    @1
    @12
    @35
    wceq
    @8
    @0
    cc
    cc
    cA
    cA
    cmin
    cc
    cidp
    @9
    cvv
    cvv
    cA
    @30
    @31
    @32
    @32
    @33
    @1
    cA
    cidp
    cfv
    #
    cA
    wceq
    @0
    @1
    @36
    cA
    @29
    cfv
    cA
    cA
    cidp
    @29
    df-idp
    fveq1i
    cc
    cA
    fvresi
    syl5eq
    adantl
    cc
    cA
    cA
    cq
    fvconst2g
    ofval
    mpdan
    @0
    cA
    @8
    subidd
    eqtrd
    @4
    @13
    vf
    @10
    @6
    @2
    @10
    wceq
    @3
    @12
    cc0
    cA
    @2
    @10
    fveq1
    eqeq1d
    rspcev
    syl2anc
    cA
    vf
    elqaa
    sylanbrc
end
