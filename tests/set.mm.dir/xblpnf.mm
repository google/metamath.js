include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cpnf.mm"
include "cbl.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "cxr.mm"
include "wb.mm"
include "pnfxr.mm"
include "elbl.mm"
include "mp3an3.mm"
include "w3a.mm"
include "cmnf.mm"
include "wne.mm"
include "cc0.mm"
include "cle.mm"
include "xmetcl.mm"
include "xmetge0.mm"
include "ge0nemnf.mm"
include "syl2anc.mm"
include "wceq.mm"
include "wn.mm"
include "ngtmnft.mm"
include "syl.mm"
include "necon2abid.mm"
include "mpbird.mm"
include "biantrurd.mm"
include "xrrebnd.mm"
include "bitr4d.mm"
include "3expa.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem xblpnf
  let cA: class A
  let cD: class D
  let cP: class P
  let cX: class X
  let vx: setvar x
  let vr: setvar r
  let vy: setvar y
  let wph: wff ph
  let cQ: class Q
  let cS: class S
  let cR: class R


  assert |- ( ( D e. ( *Met ` X ) /\ P e. X ) -> ( A e. ( P ( ball ` D ) +oo ) <-> ( A e. X /\ ( P D A ) e. RR ) ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    wa
    #
    cA
    cP
    cpnf
    cD
    cbl
    cfv
    co
    wcel
    #
    cA
    cX
    wcel
    #
    cP
    cA
    cD
    co
    #
    cpnf
    clt
    wbr
    #
    wa
    #
    @4
    @5
    cr
    wcel
    #
    wa
    @0
    @1
    cpnf
    cxr
    wcel
    @3
    @7
    wb
    pnfxr
    cA
    cD
    cP
    cpnf
    cX
    elbl
    mp3an3
    @2
    @4
    @6
    @8
    @0
    @1
    @4
    @6
    @8
    wb
    @0
    @1
    @4
    w3a
    #
    @6
    cmnf
    @5
    clt
    wbr
    #
    @6
    wa
    #
    @8
    @9
    @10
    @6
    @9
    @10
    @5
    cmnf
    wne
    #
    @9
    @5
    cxr
    wcel
    #
    cc0
    @5
    cle
    wbr
    @12
    cP
    cA
    cD
    cX
    xmetcl
    #
    cP
    cA
    cD
    cX
    xmetge0
    @5
    ge0nemnf
    syl2anc
    @9
    @10
    @5
    cmnf
    @9
    @13
    @5
    cmnf
    wceq
    @10
    wn
    wb
    @14
    @5
    ngtmnft
    syl
    necon2abid
    mpbird
    biantrurd
    @9
    @13
    @8
    @11
    wb
    @14
    @5
    xrrebnd
    syl
    bitr4d
    3expa
    pm5.32da
    bitrd
end
