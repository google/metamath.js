include "cbs.mm"
include "cfv.mm"
include "crgspn.mm"
include "eqidd.mm"
include "csubrg.mm"
include "wcel.mm"
include "wss.mm"
include "eqid.mm"
include "subrgss.mm"
include "syl.mm"
include "ssid.mm"
include "a1i.mm"
include "rgspnmin.mm"
include "rgspnssid.mm"
include "eqssd.mm"

theorem rgspnid
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cS: class S
  assume rgspnid.r: |- ( ph -> R e. Ring )
  assume rgspnid.sr: |- ( ph -> A e. ( SubRing ` R ) )
  assume rgspnid.sp: |- ( ph -> S = ( ( RingSpan ` R ) ` A ) )


  assert |- ( ph -> S = A )

  proof
    wph
    cS
    cA
    wph
    cA
    cR
    cbs
    cfv
    #
    cR
    cA
    cS
    cR
    crgspn
    cfv
    #
    rgspnid.r
    wph
    @0
    eqidd
    #
    wph
    cA
    cR
    csubrg
    cfv
    wcel
    cA
    @0
    wss
    rgspnid.sr
    cA
    @0
    cR
    @0
    eqid
    subrgss
    syl
    #
    wph
    @1
    eqidd
    #
    rgspnid.sp
    rgspnid.sr
    cA
    cA
    wss
    wph
    cA
    ssid
    a1i
    rgspnmin
    wph
    cA
    @0
    cR
    cS
    @1
    rgspnid.r
    @2
    @3
    @4
    rgspnid.sp
    rgspnssid
    eqssd
end
