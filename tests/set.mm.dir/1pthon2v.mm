include "cuhgr.mm"
include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "w3a.mm"
include "cpthson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wex.mm"
include "wi.mm"
include "wceq.mm"
include "simpl.mm"
include "anim2i.mm"
include "3adant3.mm"
include "adantl.mm"
include "0pthonv.mm"
include "syl.mm"
include "wb.mm"
include "oveq2.mm"
include "eqcoms.mm"
include "breqd.mm"
include "2exbidv.mm"
include "adantr.mm"
include "mpbird.mm"
include "ex.mm"
include "wne.mm"
include "ciedg.mm"
include "cdm.mm"
include "cedg.mm"
include "eleq2i.mm"
include "eqid.mm"
include "uhgredgiedgb.mm"
include "syl5bb.mm"
include "3ad2ant1.mm"
include "cs1.mm"
include "cvv.mm"
include "cword.mm"
include "cs2.mm"
include "s1cli.mm"
include "s2cli.mm"
include "pm3.2i.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "csn.mm"
include "eqneqall.mm"
include "com12.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "sseq2.mm"
include "biimpa.mm"
include "1pthond.mm"
include "breq12.mm"
include "spc2egv.mm"
include "mpsyl.mm"
include "exp44.mm"
include "rexlimdv.mm"
include "sylbid.mm"
include "3exp.mm"
include "com34.mm"
include "3imp.mm"
include "pm2.61ine.mm"

theorem 1pthon2v
  let cA: class A
  let cB: class B
  let ve: setvar e
  let vf: setvar f
  let cE: class E
  let cG: class G
  let cV: class V
  let vp: setvar p
  let vi: setvar i
  assume 1pthon2v.v: |- V = ( Vtx ` G )
  assume 1pthon2v.e: |- E = ( Edg ` G )

  disjoint A e
  disjoint A f
  disjoint A p
  disjoint e f
  disjoint e p
  disjoint f p
  disjoint B e
  disjoint B f
  disjoint B p
  disjoint G e
  disjoint G f
  disjoint G p
  disjoint V e
  disjoint A i
  disjoint e i
  disjoint f i
  disjoint i p
  disjoint B i
  disjoint G i
  disjoint V i
  assert |- ( ( G e. UHGraph /\ ( A e. V /\ B e. V ) /\ E. e e. E { A , B } C_ e ) -> E. f E. p f ( A ( PathsOn ` G ) B ) p )

  proof
    cG
    cuhgr
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    wa
    #
    cA
    cB
    cpr
    #
    ve
    cv
    #
    wss
    #
    ve
    cE
    wrex
    #
    w3a
    #
    vf
    cv
    #
    vp
    cv
    #
    cA
    cB
    cG
    cpthson
    cfv
    #
    co
    #
    wbr
    #
    vp
    wex
    vf
    wex
    #
    wi
    cA
    cB
    cA
    cB
    wceq
    #
    @8
    @14
    @15
    @8
    wa
    #
    @14
    @9
    @10
    cA
    cA
    @11
    co
    #
    wbr
    #
    vp
    wex
    vf
    wex
    #
    @16
    @0
    @1
    wa
    #
    @19
    @8
    @20
    @15
    @0
    @3
    @20
    @7
    @3
    @1
    @0
    @1
    @2
    simpl
    anim2i
    3adant3
    adantl
    @1
    @19
    @0
    vf
    cG
    cA
    cV
    vp
    1pthon2v.v
    0pthonv
    adantl
    syl
    @15
    @14
    @19
    wb
    @8
    @15
    @13
    @18
    vf
    vp
    @15
    @12
    @17
    @9
    @10
    @12
    @17
    wceq
    cB
    cA
    cB
    cA
    cA
    @11
    oveq2
    eqcoms
    breqd
    2exbidv
    adantr
    mpbird
    ex
    @8
    cA
    cB
    wne
    #
    @14
    @0
    @3
    @7
    @21
    @14
    wi
    @0
    @3
    @21
    @7
    @14
    @0
    @3
    @21
    @7
    @14
    wi
    @0
    @3
    @21
    w3a
    #
    @6
    @14
    ve
    cE
    @22
    @5
    cE
    wcel
    #
    @5
    vi
    cv
    #
    cG
    ciedg
    cfv
    #
    cfv
    #
    wceq
    #
    vi
    @25
    cdm
    #
    wrex
    #
    @6
    @14
    wi
    #
    @0
    @3
    @23
    @29
    wb
    @21
    @23
    @5
    cG
    cedg
    cfv
    #
    wcel
    @0
    @29
    cE
    @31
    @5
    1pthon2v.e
    eleq2i
    vi
    @5
    cG
    @25
    @25
    eqid
    #
    uhgredgiedgb
    syl5bb
    3ad2ant1
    @22
    @27
    @30
    vi
    @28
    @22
    @24
    @28
    wcel
    #
    @27
    @6
    @14
    @24
    cs1
    #
    cvv
    cword
    #
    wcel
    #
    cA
    cB
    cs2
    #
    @35
    wcel
    #
    wa
    @22
    @33
    @27
    wa
    #
    @6
    wa
    #
    wa
    #
    @34
    @37
    @12
    wbr
    #
    @14
    @36
    @38
    @24
    s1cli
    cA
    cB
    s2cli
    pm3.2i
    @41
    @37
    @34
    cG
    @25
    @24
    cV
    cA
    cB
    @37
    eqid
    @34
    eqid
    @1
    @2
    @0
    @21
    @40
    simpl2l
    @1
    @2
    @0
    @21
    @40
    simpl2r
    @41
    @15
    @26
    cA
    csn
    wceq
    #
    @22
    @15
    @43
    wi
    #
    @40
    @21
    @0
    @44
    @3
    @15
    @21
    @43
    @43
    cA
    cB
    eqneqall
    com12
    3ad2ant3
    adantr
    imp
    @41
    @4
    @26
    wss
    #
    @21
    @40
    @45
    @22
    @39
    @6
    @45
    @27
    @6
    @45
    wb
    @33
    @5
    @26
    @4
    sseq2
    adantl
    biimpa
    adantl
    adantr
    1pthon2v.v
    @32
    1pthond
    @13
    @42
    vf
    vp
    @34
    @37
    @35
    @35
    @9
    @34
    @10
    @37
    @12
    breq12
    spc2egv
    mpsyl
    exp44
    rexlimdv
    sylbid
    rexlimdv
    3exp
    com34
    3imp
    com12
    pm2.61ine
end
