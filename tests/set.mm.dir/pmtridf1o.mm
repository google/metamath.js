include "wf1o.mm"
include "wceq.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "cpr.mm"
include "cpmtr.mm"
include "cfv.mm"
include "cif.mm"
include "iftrue.mm"
include "adantl.mm"
include "syl5eq.mm"
include "f1oi.mm"
include "a1i.mm"
include "f1oeq1.mm"
include "biimpar.mm"
include "syl2anc.mm"
include "wne.mm"
include "crn.mm"
include "wcel.mm"
include "wn.mm"
include "simpr.mm"
include "neneqd.mm"
include "iffalse.mm"
include "syl.mm"
include "wss.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "adantr.mm"
include "prssd.mm"
include "pr2nelem.mm"
include "syl3anc.mm"
include "eqid.mm"
include "pmtrrn.mm"
include "eqeltrd.mm"
include "pmtrff1o.mm"
include "pm2.61dane.mm"

theorem pmtridf1o
  let wph: wff ph
  let cA: class A
  let cT: class T
  let cV: class V
  let cX: class X
  let cY: class Y
  assume pmtridf1o.a: |- ( ph -> A e. V )
  assume pmtridf1o.x: |- ( ph -> X e. A )
  assume pmtridf1o.y: |- ( ph -> Y e. A )
  assume pmtridf1o.t: |- T = if ( X = Y , ( _I |` A ) , ( ( pmTrsp ` A ) ` { X , Y } ) )


  assert |- ( ph -> T : A -1-1-onto-> A )

  proof
    wph
    cA
    cA
    cT
    wf1o
    #
    cX
    cY
    wph
    cX
    cY
    wceq
    #
    wa
    #
    cT
    cid
    cA
    cres
    #
    wceq
    #
    cA
    cA
    @3
    wf1o
    #
    @0
    @2
    cT
    @1
    @3
    cX
    cY
    cpr
    #
    cA
    cpmtr
    cfv
    #
    cfv
    #
    cif
    #
    @3
    pmtridf1o.t
    @1
    @9
    @3
    wceq
    wph
    @1
    @3
    @8
    iftrue
    adantl
    syl5eq
    @5
    @2
    cA
    f1oi
    a1i
    @4
    @0
    @5
    cA
    cA
    cT
    @3
    f1oeq1
    biimpar
    syl2anc
    wph
    cX
    cY
    wne
    #
    wa
    #
    cT
    @7
    crn
    #
    wcel
    @0
    @11
    cT
    @8
    @12
    @11
    cT
    @9
    @8
    pmtridf1o.t
    @11
    @1
    wn
    @9
    @8
    wceq
    @11
    cX
    cY
    wph
    @10
    simpr
    #
    neneqd
    @1
    @3
    @8
    iffalse
    syl
    syl5eq
    @11
    cA
    cV
    wcel
    #
    @6
    cA
    wss
    @6
    c2o
    cen
    wbr
    #
    @8
    @12
    wcel
    wph
    @14
    @10
    pmtridf1o.a
    adantr
    @11
    cX
    cY
    cA
    wph
    cX
    cA
    wcel
    #
    @10
    pmtridf1o.x
    adantr
    #
    wph
    cY
    cA
    wcel
    #
    @10
    pmtridf1o.y
    adantr
    #
    prssd
    @11
    @16
    @18
    @10
    @15
    @17
    @19
    @13
    cX
    cY
    cA
    cA
    pr2nelem
    syl3anc
    cA
    @6
    @12
    @7
    cV
    @7
    eqid
    #
    @12
    eqid
    #
    pmtrrn
    syl3anc
    eqeltrd
    cA
    @12
    @7
    cT
    @20
    @21
    pmtrff1o
    syl
    pm2.61dane
end
