include "csn.mm"
include "cfv.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cminusg.mm"
include "clmod.mm"
include "wcel.mm"
include "eqid.mm"
include "lspsnneg.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "adantr.mm"
include "cgrp.mm"
include "wb.mm"
include "lmodgrp.mm"
include "syl.mm"
include "grpinvid1.mm"
include "syl3anc.mm"
include "biimpar.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"

theorem lmodindp1
  let wph: wff ph
  let c.pl: class .+
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lmodindp1.v: |- V = ( Base ` W )
  assume lmodindp1.p: |- .+ = ( +g ` W )
  assume lmodindp1.o: |- .0. = ( 0g ` W )
  assume lmodindp1.n: |- N = ( LSpan ` W )
  assume lmodindp1.w: |- ( ph -> W e. LMod )
  assume lmodindp1.x: |- ( ph -> X e. V )
  assume lmodindp1.y: |- ( ph -> Y e. V )
  assume lmodindp1.q: |- ( ph -> ( N ` { X } ) =/= ( N ` { Y } ) )


  assert |- ( ph -> ( X .+ Y ) =/= .0. )

  proof
    wph
    cX
    csn
    cN
    cfv
    #
    cY
    csn
    #
    cN
    cfv
    #
    wne
    cX
    cY
    c.pl
    co
    #
    c.0
    wne
    lmodindp1.q
    wph
    @3
    c.0
    @0
    @2
    wph
    @3
    c.0
    wceq
    #
    @0
    @2
    wceq
    wph
    @4
    wa
    #
    @0
    cX
    cW
    cminusg
    cfv
    #
    cfv
    #
    csn
    #
    cN
    cfv
    #
    @2
    wph
    @0
    @9
    wceq
    @4
    wph
    @9
    @0
    wph
    cW
    clmod
    wcel
    #
    cX
    cV
    wcel
    #
    @9
    @0
    wceq
    lmodindp1.w
    lmodindp1.x
    @6
    cN
    cV
    cW
    cX
    lmodindp1.v
    @6
    eqid
    #
    lmodindp1.n
    lspsnneg
    syl2anc
    eqcomd
    adantr
    @5
    @8
    @1
    cN
    @5
    @7
    cY
    wph
    @7
    cY
    wceq
    #
    @4
    wph
    cW
    cgrp
    wcel
    #
    @11
    cY
    cV
    wcel
    @13
    @4
    wb
    wph
    @10
    @14
    lmodindp1.w
    cW
    lmodgrp
    syl
    lmodindp1.x
    lmodindp1.y
    cV
    c.pl
    cW
    @6
    cX
    cY
    c.0
    lmodindp1.v
    lmodindp1.p
    lmodindp1.o
    @12
    grpinvid1
    syl3anc
    biimpar
    sneqd
    fveq2d
    eqtrd
    ex
    necon3d
    mpd
end
