include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "cpr.mm"
include "cpmtr.mm"
include "cif.mm"
include "simpr.mm"
include "iftrued.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "wcel.mm"
include "fvresi.mm"
include "syl.mm"
include "adantr.mm"
include "3eqtrd.mm"
include "wne.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "eqid.mm"
include "pmtrprfv.mm"
include "syl13anc.mm"
include "eqtrd.mm"
include "pm2.61dane.mm"

theorem pmtridfv1
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


  assert |- ( ph -> ( T ` X ) = Y )

  proof
    wph
    cX
    cT
    cfv
    #
    cY
    wceq
    cX
    cY
    wph
    cX
    cY
    wceq
    #
    wa
    #
    @0
    cX
    cid
    cA
    cres
    #
    cfv
    #
    cX
    cY
    @2
    cX
    cT
    @3
    @2
    cT
    @1
    @3
    cX
    cY
    cpr
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
    @2
    @1
    @3
    @6
    wph
    @1
    simpr
    #
    iftrued
    syl5eq
    fveq1d
    wph
    @4
    cX
    wceq
    #
    @1
    wph
    cX
    cA
    wcel
    #
    @9
    pmtridf1o.x
    cA
    cX
    fvresi
    syl
    adantr
    @8
    3eqtrd
    wph
    cX
    cY
    wne
    #
    wa
    #
    @0
    cX
    @6
    cfv
    #
    cY
    @12
    cX
    cT
    @6
    @12
    cT
    @7
    @6
    pmtridf1o.t
    @12
    @1
    @3
    @6
    @12
    cX
    cY
    wph
    @11
    simpr
    #
    neneqd
    iffalsed
    syl5eq
    fveq1d
    @12
    cA
    cV
    wcel
    #
    @10
    cY
    cA
    wcel
    #
    @11
    @13
    cY
    wceq
    wph
    @15
    @11
    pmtridf1o.a
    adantr
    wph
    @10
    @11
    pmtridf1o.x
    adantr
    wph
    @16
    @11
    pmtridf1o.y
    adantr
    @14
    cA
    @5
    cV
    cX
    cY
    @5
    eqid
    pmtrprfv
    syl13anc
    eqtrd
    pm2.61dane
end
