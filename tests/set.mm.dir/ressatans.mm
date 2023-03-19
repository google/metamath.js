include "cr.mm"
include "c1.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "wcel.mm"
include "cc.mm"
include "crab.mm"
include "wss.mm"
include "wral.mm"
include "ax-resscn.mm"
include "cmnf.mm"
include "cc0.mm"
include "cioc.mm"
include "cdif.mm"
include "1re.mm"
include "resqcl.mm"
include "readdcl.mm"
include "sylancr.mm"
include "recnd.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "0re.mm"
include "a1i.mm"
include "0lt1.mm"
include "sqge0.mm"
include "wb.mm"
include "addge01.mm"
include "mpbid.mm"
include "ltletrd.mm"
include "ltnle.mm"
include "cxr.mm"
include "w3a.mm"
include "mnfxr.mm"
include "elioc2.mm"
include "mp2an.mm"
include "simp3bi.mm"
include "nsyl.mm"
include "eldifd.mm"
include "syl6eleqr.mm"
include "rgen.mm"
include "ssrab.mm"
include "mpbir2an.mm"
include "sseqtr4i.mm"

theorem ressatans
  let vy: setvar y
  let cD: class D
  let cS: class S
  let cA: class A
  let vx: setvar x
  assume atansopn.d: |- D = ( CC \ ( -oo (,] 0 ) )
  assume atansopn.s: |- S = { y e. CC | ( 1 + ( y ^ 2 ) ) e. D }

  disjoint D y
  disjoint A y
  disjoint x y
  disjoint D x
  disjoint S x
  assert |- RR C_ S

  proof
    cr
    c1
    vy
    cv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    cD
    wcel
    #
    vy
    cc
    crab
    #
    cS
    cr
    @4
    wss
    cr
    cc
    wss
    @3
    vy
    cr
    wral
    ax-resscn
    @3
    vy
    cr
    @0
    cr
    wcel
    #
    @2
    cc
    cmnf
    cc0
    cioc
    co
    #
    cdif
    cD
    @5
    @2
    cc
    @6
    @5
    @2
    @5
    c1
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    1re
    @0
    resqcl
    #
    c1
    @1
    readdcl
    sylancr
    #
    recnd
    @5
    @2
    cc0
    cle
    wbr
    #
    @2
    @6
    wcel
    #
    @5
    cc0
    @2
    clt
    wbr
    #
    @12
    wn
    #
    @5
    cc0
    c1
    @2
    cc0
    cr
    wcel
    #
    @5
    0re
    a1i
    @7
    @5
    1re
    a1i
    @11
    cc0
    c1
    clt
    wbr
    @5
    0lt1
    a1i
    @5
    cc0
    @1
    cle
    wbr
    #
    c1
    @2
    cle
    wbr
    #
    @0
    sqge0
    @5
    @7
    @8
    @17
    @18
    wb
    1re
    @10
    c1
    @1
    addge01
    sylancr
    mpbid
    ltletrd
    @5
    @16
    @9
    @14
    @15
    wb
    0re
    @11
    cc0
    @2
    ltnle
    sylancr
    mpbid
    @13
    @9
    cmnf
    @2
    clt
    wbr
    #
    @12
    cmnf
    cxr
    wcel
    @16
    @13
    @9
    @19
    @12
    w3a
    wb
    mnfxr
    0re
    cmnf
    cc0
    @2
    elioc2
    mp2an
    simp3bi
    nsyl
    eldifd
    atansopn.d
    syl6eleqr
    rgen
    @3
    vy
    cc
    cr
    ssrab
    mpbir2an
    atansopn.s
    sseqtr4i
end
