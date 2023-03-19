include "wcel.mm"
include "cneg.mm"
include "crp.mm"
include "cmnf.mm"
include "cc0.mm"
include "cioc.mm"
include "co.mm"
include "wn.mm"
include "cc.mm"
include "cdif.mm"
include "eldifn.mm"
include "eleq2s.mm"
include "wa.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "rpre.mm"
include "wb.mm"
include "wi.mm"
include "ellogdm.mm"
include "simplbi.mm"
include "negreb.mm"
include "syl.mm"
include "syl5ib.mm"
include "imp.mm"
include "mnflt.mm"
include "rpgt0.mm"
include "adantl.mm"
include "lt0neg1d.mm"
include "mpbird.mm"
include "0re.mm"
include "ltle.mm"
include "sylancl.mm"
include "mpd.mm"
include "cxr.mm"
include "w3a.mm"
include "mnfxr.mm"
include "elioc2.mm"
include "mp2an.mm"
include "syl3anbrc.mm"
include "mtand.mm"

theorem logdmnrp
  let cA: class A
  let cD: class D
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume logcn.d: |- D = ( CC \ ( -oo (,] 0 ) )


  assert |- ( A e. D -> -. -u A e. RR+ )

  proof
    cA
    cD
    wcel
    #
    cA
    cneg
    #
    crp
    wcel
    #
    cA
    cmnf
    cc0
    cioc
    co
    #
    wcel
    #
    @4
    wn
    cA
    cc
    @3
    cdif
    cD
    cA
    cc
    @3
    eldifn
    logcn.d
    eleq2s
    @0
    @2
    wa
    #
    cA
    cr
    wcel
    #
    cmnf
    cA
    clt
    wbr
    #
    cA
    cc0
    cle
    wbr
    #
    @4
    @0
    @2
    @6
    @2
    @1
    cr
    wcel
    #
    @0
    @6
    @1
    rpre
    @0
    cA
    cc
    wcel
    #
    @9
    @6
    wb
    @0
    @10
    @6
    cA
    crp
    wcel
    wi
    cA
    cD
    logcn.d
    ellogdm
    simplbi
    cA
    negreb
    syl
    syl5ib
    imp
    #
    @5
    @6
    @7
    @11
    cA
    mnflt
    syl
    @5
    cA
    cc0
    clt
    wbr
    #
    @8
    @5
    @12
    cc0
    @1
    clt
    wbr
    #
    @2
    @13
    @0
    @1
    rpgt0
    adantl
    @5
    cA
    @11
    lt0neg1d
    mpbird
    @5
    @6
    cc0
    cr
    wcel
    #
    @12
    @8
    wi
    @11
    0re
    cA
    cc0
    ltle
    sylancl
    mpd
    cmnf
    cxr
    wcel
    @14
    @4
    @6
    @7
    @8
    w3a
    wb
    mnfxr
    0re
    cmnf
    cc0
    cA
    elioc2
    mp2an
    syl3anbrc
    mtand
end
