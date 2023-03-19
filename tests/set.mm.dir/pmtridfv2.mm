include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "wcel.mm"
include "fvresi.mm"
include "syl.mm"
include "adantr.mm"
include "cpr.mm"
include "cpmtr.mm"
include "cif.mm"
include "simpr.mm"
include "iftrued.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "3eqtr4d.mm"
include "wne.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "eqid.mm"
include "pmtrprfv2.mm"
include "syl13anc.mm"
include "eqtrd.mm"
include "pm2.61dane.mm"

theorem pmtridfv2
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


  assert |- ( ph -> ( T ` Y ) = X )

  proof
    wph
    cY
    cT
    cfv
    #
    cX
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
    cY
    cid
    cA
    cres
    #
    cfv
    #
    cY
    @0
    cX
    wph
    @4
    cY
    wceq
    #
    @1
    wph
    cY
    cA
    wcel
    #
    @5
    pmtridf1o.y
    cA
    cY
    fvresi
    syl
    adantr
    @2
    cY
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
    @8
    wph
    @1
    simpr
    #
    iftrued
    syl5eq
    fveq1d
    @10
    3eqtr4d
    wph
    cX
    cY
    wne
    #
    wa
    #
    @0
    cY
    @8
    cfv
    #
    cX
    @12
    cY
    cT
    @8
    @12
    cT
    @9
    @8
    pmtridf1o.t
    @12
    @1
    @3
    @8
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
    cX
    cA
    wcel
    #
    @6
    @11
    @13
    cX
    wceq
    wph
    @15
    @11
    pmtridf1o.a
    adantr
    wph
    @16
    @11
    pmtridf1o.x
    adantr
    wph
    @6
    @11
    pmtridf1o.y
    adantr
    @14
    cA
    @7
    cV
    cX
    cY
    @7
    eqid
    pmtrprfv2
    syl13anc
    eqtrd
    pm2.61dane
end
