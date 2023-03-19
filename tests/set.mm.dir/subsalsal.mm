include "cvv.mm"
include "cuni.mm"
include "wcel.mm"
include "crest.mm"
include "ovexi.mm"
include "a1i.mm"
include "c0.mm"
include "co.mm"
include "csalg.mm"
include "0sald.mm"
include "cin.mm"
include "0in.mm"
include "eqcomi.mm"
include "elrestd.mm"
include "syl6eleqr.mm"
include "eqid.mm"
include "cv.mm"
include "wa.mm"
include "wceq.mm"
include "wrex.mm"
include "cdif.mm"
include "id.mm"
include "syl6eleq.mm"
include "adantl.mm"
include "wb.mm"
include "elrest.mm"
include "syl2anc.mm"
include "adantr.mm"
include "mpbid.mm"
include "wi.mm"
include "w3a.mm"
include "3adant3.mm"
include "3ad2ant1.mm"
include "simpr.mm"
include "saldifcld.mm"
include "unieqi.mm"
include "restuni3.mm"
include "eqtrd.mm"
include "difeq12d.mm"
include "indifdir.mm"
include "eleq12d.mm"
include "3adant2.mm"
include "mpbird.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "cn.mm"
include "wf.mm"
include "subsaliuncl.mm"
include "issalnnd.mm"

theorem subsalsal
  let wph: wff ph
  let cD: class D
  let cS: class S
  let cT: class T
  let cV: class V
  let vn: setvar n
  let vy: setvar y
  let vf: setvar f
  let vx: setvar x
  let vk: setvar k
  assume subsalsal.1: |- ( ph -> S e. SAlg )
  assume subsalsal.2: |- ( ph -> D e. V )
  assume subsalsal.3: |- T = ( S |`t D )


  assert |- ( ph -> T e. SAlg )

  proof
    wph
    vx
    cT
    vf
    vn
    cvv
    cT
    cuni
    #
    cT
    cvv
    wcel
    wph
    cT
    cS
    cD
    crest
    subsalsal.3
    ovexi
    a1i
    wph
    c0
    cS
    cD
    crest
    co
    #
    cT
    wph
    c0
    cD
    cS
    csalg
    cV
    c0
    subsalsal.1
    subsalsal.2
    wph
    cS
    subsalsal.1
    0sald
    c0
    cD
    cin
    c0
    cD
    0in
    eqcomi
    elrestd
    subsalsal.3
    syl6eleqr
    @0
    eqid
    wph
    vx
    cv
    #
    cT
    wcel
    #
    wa
    #
    @2
    vy
    cv
    #
    cD
    cin
    #
    wceq
    #
    vy
    cS
    wrex
    #
    @0
    @2
    cdif
    #
    cT
    wcel
    #
    @4
    @2
    @1
    wcel
    #
    @8
    @3
    @11
    wph
    @3
    @2
    cT
    @1
    @3
    id
    subsalsal.3
    syl6eleq
    adantl
    wph
    @11
    @8
    wb
    #
    @3
    wph
    cS
    csalg
    wcel
    #
    cD
    cV
    wcel
    #
    @12
    subsalsal.1
    subsalsal.2
    vy
    @2
    cD
    cS
    csalg
    cV
    elrest
    syl2anc
    adantr
    mpbid
    wph
    @8
    @10
    wi
    @3
    wph
    @7
    @10
    vy
    cS
    wph
    @5
    cS
    wcel
    #
    @7
    @10
    wph
    @15
    @7
    w3a
    #
    @10
    cS
    cuni
    #
    @5
    cdif
    #
    cD
    cin
    #
    @1
    wcel
    #
    @16
    @19
    cD
    cS
    csalg
    cV
    @18
    wph
    @15
    @13
    @7
    wph
    @13
    @15
    subsalsal.1
    adantr
    #
    3adant3
    wph
    @15
    @14
    @7
    subsalsal.2
    3ad2ant1
    wph
    @15
    @18
    cS
    wcel
    @7
    wph
    @15
    wa
    cS
    @5
    @21
    wph
    @15
    simpr
    saldifcld
    3adant3
    @19
    eqid
    elrestd
    wph
    @7
    @10
    @20
    wb
    @15
    wph
    @7
    wa
    #
    @9
    @19
    cT
    @1
    @22
    @9
    @17
    cD
    cin
    #
    @6
    cdif
    #
    @19
    @22
    @0
    @23
    @2
    @6
    wph
    @0
    @23
    wceq
    @7
    wph
    @0
    @1
    cuni
    #
    @23
    @0
    @25
    wceq
    wph
    cT
    @1
    subsalsal.3
    unieqi
    a1i
    wph
    cS
    cD
    csalg
    cV
    subsalsal.1
    subsalsal.2
    restuni3
    eqtrd
    adantr
    wph
    @7
    simpr
    difeq12d
    @24
    @19
    wceq
    @22
    @19
    @24
    @17
    @5
    cD
    indifdir
    eqcomi
    a1i
    eqtrd
    cT
    @1
    wceq
    @22
    subsalsal.3
    a1i
    eleq12d
    3adant2
    mpbird
    3exp
    rexlimdv
    adantr
    mpd
    wph
    cn
    cT
    vf
    cv
    #
    wf
    #
    wa
    cD
    cS
    cT
    vn
    @26
    cV
    wph
    @13
    @27
    subsalsal.1
    adantr
    wph
    @14
    @27
    subsalsal.2
    adantr
    subsalsal.3
    wph
    @27
    simpr
    subsaliuncl
    issalnnd
end
