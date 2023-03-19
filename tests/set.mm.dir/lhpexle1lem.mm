include "wcel.mm"
include "wbr.mm"
include "cv.mm"
include "wne.mm"
include "w3a.mm"
include "wrex.mm"
include "wn.mm"
include "wa.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "simplr.mm"
include "simpllr.mm"
include "nelne2.mm"
include "syl2anc.mm"
include "3jca.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "nbrne2.mm"
include "reximdv.mm"
include "pm2.61dda.mm"

theorem lhpexle1lem
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let vp: setvar p
  assume lhpexle1lem.1: |- ( ph -> E. p e. A ( p .<_ W /\ ps ) )
  assume lhpexle1lem.2: |- ( ( ph /\ ( X e. A /\ X .<_ W ) ) -> E. p e. A ( p .<_ W /\ ps /\ p =/= X ) )

  disjoint .<_ p
  disjoint A p
  disjoint W p
  disjoint X p
  disjoint p ph
  assert |- ( ph -> E. p e. A ( p .<_ W /\ ps /\ p =/= X ) )

  proof
    wph
    cX
    cA
    wcel
    #
    cX
    cW
    c.le
    wbr
    #
    vp
    cv
    #
    cW
    c.le
    wbr
    #
    wps
    @2
    cX
    wne
    #
    w3a
    #
    vp
    cA
    wrex
    #
    wph
    @0
    wn
    #
    wa
    #
    @3
    wps
    wa
    #
    vp
    cA
    wrex
    #
    @6
    wph
    @10
    @7
    lhpexle1lem.1
    adantr
    @8
    @9
    @5
    vp
    cA
    @8
    @2
    cA
    wcel
    #
    wa
    #
    @9
    @5
    @12
    @9
    wa
    #
    @3
    wps
    @4
    @12
    @3
    wps
    simprl
    @12
    @3
    wps
    simprr
    @13
    @11
    @7
    @4
    @8
    @11
    @9
    simplr
    wph
    @7
    @11
    @9
    simpllr
    @2
    cX
    cA
    nelne2
    syl2anc
    3jca
    ex
    reximdva
    mpd
    wph
    @1
    wn
    #
    wa
    #
    @10
    @6
    wph
    @10
    @14
    lhpexle1lem.1
    adantr
    @15
    @9
    @5
    vp
    cA
    @15
    @9
    @5
    @15
    @9
    wa
    #
    @3
    wps
    @4
    @15
    @3
    wps
    simprl
    #
    @15
    @3
    wps
    simprr
    @16
    @3
    @14
    @4
    @17
    wph
    @14
    @9
    simplr
    @2
    cX
    cW
    c.le
    nbrne2
    syl2anc
    3jca
    ex
    reximdv
    mpd
    lhpexle1lem.2
    pm2.61dda
end
