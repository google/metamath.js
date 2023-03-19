include "ci.mm"
include "caa.mm"
include "wcel.mm"
include "cc.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cz.mm"
include "cply.mm"
include "c0p.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "ax-icn.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cmpt.mm"
include "wne.mm"
include "wtru.mm"
include "cxp.mm"
include "cof.mm"
include "cvv.mm"
include "cnex.mm"
include "a1i.mm"
include "sqcl.mm"
include "adantl.mm"
include "wa.mm"
include "ax-1cn.mm"
include "eqidd.mm"
include "fconstmpt.mm"
include "offval2.mm"
include "wss.mm"
include "cn0.mm"
include "zsscn.mm"
include "1z.mm"
include "2nn0.mm"
include "plypow.mm"
include "mp3an.mm"
include "plyconst.mm"
include "mp2an.mm"
include "zaddcl.mm"
include "plyadd.mm"
include "eqeltrrd.mm"
include "trud.mm"
include "0cn.mm"
include "sq0i.mm"
include "oveq1d.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "eqid.mm"
include "1ex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "ax-1ne0.mm"
include "eqnetri.mm"
include "ne0p.mm"
include "eldifsn.mm"
include "mpbir2an.mm"
include "cneg.mm"
include "oveq1.mm"
include "i2.mm"
include "neg1cn.mm"
include "1pneg1e0.mm"
include "addcomli.mm"
include "c0ex.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "elaa.mm"

theorem iaa
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  let cP: class P
  let wph: wff ph
  let cF: class F
  let cK: class K
  let cN: class N
  let cR: class R


  assert |- _i e. AA

  proof
    ci
    caa
    wcel
    ci
    cc
    wcel
    #
    ci
    vf
    cv
    #
    cfv
    #
    cc0
    wceq
    #
    vf
    cz
    cply
    cfv
    #
    c0p
    csn
    cdif
    #
    wrex
    #
    ax-icn
    vz
    cc
    vz
    cv
    #
    c2
    cexp
    co
    #
    c1
    caddc
    co
    #
    cmpt
    #
    @5
    wcel
    #
    ci
    @10
    cfv
    #
    cc0
    wceq
    #
    @6
    @11
    @10
    @4
    wcel
    #
    @10
    c0p
    wne
    #
    @14
    wtru
    vz
    cc
    @8
    cmpt
    #
    cc
    c1
    csn
    cxp
    #
    caddc
    cof
    co
    @10
    @4
    wtru
    vz
    cc
    @8
    c1
    caddc
    @16
    @17
    cvv
    cc
    cc
    cc
    cvv
    wcel
    wtru
    cnex
    a1i
    @7
    cc
    wcel
    #
    @8
    cc
    wcel
    wtru
    @7
    sqcl
    adantl
    c1
    cc
    wcel
    wtru
    @18
    wa
    ax-1cn
    a1i
    wtru
    @16
    eqidd
    @17
    vz
    cc
    c1
    cmpt
    wceq
    wtru
    vz
    cc
    c1
    fconstmpt
    a1i
    offval2
    wtru
    vx
    vy
    cz
    @16
    @17
    @16
    @4
    wcel
    #
    wtru
    cz
    cc
    wss
    #
    c1
    cz
    wcel
    #
    c2
    cn0
    wcel
    @19
    zsscn
    1z
    2nn0
    vz
    cz
    c2
    plypow
    mp3an
    a1i
    @17
    @4
    wcel
    #
    wtru
    @20
    @21
    @22
    zsscn
    1z
    c1
    cz
    plyconst
    mp2an
    a1i
    vx
    cv
    #
    cz
    wcel
    vy
    cv
    #
    cz
    wcel
    wa
    @23
    @24
    caddc
    co
    cz
    wcel
    wtru
    @23
    @24
    zaddcl
    adantl
    plyadd
    eqeltrrd
    trud
    cc0
    cc
    wcel
    #
    cc0
    @10
    cfv
    #
    cc0
    wne
    @15
    0cn
    @26
    c1
    cc0
    @25
    @26
    c1
    wceq
    0cn
    vz
    cc0
    @9
    c1
    cc
    @10
    @7
    cc0
    wceq
    #
    @9
    cc0
    c1
    caddc
    co
    c1
    @27
    @8
    cc0
    c1
    caddc
    @7
    sq0i
    oveq1d
    0p1e1
    syl6eq
    @10
    eqid
    #
    1ex
    fvmpt
    ax-mp
    ax-1ne0
    eqnetri
    cc0
    @10
    ne0p
    mp2an
    @10
    @4
    c0p
    eldifsn
    mpbir2an
    @0
    @13
    ax-icn
    vz
    ci
    @9
    cc0
    cc
    @10
    @7
    ci
    wceq
    #
    @9
    c1
    cneg
    #
    c1
    caddc
    co
    cc0
    @29
    @8
    @30
    c1
    caddc
    @29
    @8
    ci
    c2
    cexp
    co
    @30
    @7
    ci
    c2
    cexp
    oveq1
    i2
    syl6eq
    oveq1d
    c1
    @30
    cc0
    ax-1cn
    neg1cn
    1pneg1e0
    addcomli
    syl6eq
    @28
    c0ex
    fvmpt
    ax-mp
    @3
    @13
    vf
    @10
    @5
    @1
    @10
    wceq
    @2
    @12
    cc0
    ci
    @1
    @10
    fveq1
    eqeq1d
    rspcev
    mp2an
    ci
    vf
    elaa
    mpbir2an
end
