include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "c0.mm"
include "cun.mm"
include "wcel.mm"
include "wa.mm"
include "cdom.mm"
include "cpw.mm"
include "cdif.mm"
include "mrissd.mm"
include "dif0.mm"
include "syl6sseqr.mm"
include "cfv.mm"
include "un0.mm"
include "fveq2i.mm"
include "syl5eqel.mm"
include "mreexexd.mm"
include "simprrl.mm"
include "wss.mm"
include "simprl.mm"
include "elpwid.mm"
include "wi.mm"
include "cvv.mm"
include "cmre.mm"
include "elfvexd.mm"
include "ssexd.mm"
include "ssdomg.mm"
include "syl.mm"
include "adantr.mm"
include "mpd.mm"
include "endomtr.mm"
include "syl2anc.mm"
include "rexlimddv.mm"

theorem mreexdomd
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cS: class S
  let cT: class T
  let cI: class I
  let cN: class N
  let cX: class X
  let vs: setvar s
  let vi: setvar i
  assume mreexdomd.1: |- ( ph -> A e. ( Moore ` X ) )
  assume mreexdomd.2: |- N = ( mrCls ` A )
  assume mreexdomd.3: |- I = ( mrInd ` A )
  assume mreexdomd.4: |- ( ph -> A. s e. ~P X A. y e. X A. z e. ( ( N ` ( s u. { y } ) ) \ ( N ` s ) ) y e. ( N ` ( s u. { z } ) ) )
  assume mreexdomd.5: |- ( ph -> S C_ ( N ` T ) )
  assume mreexdomd.6: |- ( ph -> T C_ X )
  assume mreexdomd.7: |- ( ph -> ( S e. Fin \/ T e. Fin ) )
  assume mreexdomd.8: |- ( ph -> S e. I )

  disjoint X s
  disjoint s y
  disjoint s z
  disjoint X y
  disjoint X z
  disjoint y z
  disjoint ph s
  disjoint ph y
  disjoint ph z
  disjoint I s
  disjoint I y
  disjoint I z
  disjoint N s
  disjoint N y
  disjoint N z
  disjoint S i
  disjoint T i
  disjoint i ph
  disjoint I i
  assert |- ( ph -> S ~<_ T )

  proof
    wph
    cS
    vi
    cv
    #
    cen
    wbr
    #
    @0
    c0
    cun
    cI
    wcel
    #
    wa
    #
    cS
    cT
    cdom
    wbr
    #
    vi
    cT
    cpw
    #
    wph
    vy
    vz
    cA
    cS
    cT
    c0
    cI
    cN
    cX
    vs
    vi
    mreexdomd.1
    mreexdomd.2
    mreexdomd.3
    mreexdomd.4
    wph
    cS
    cX
    cX
    c0
    cdif
    #
    wph
    cA
    cS
    cI
    cX
    mreexdomd.3
    mreexdomd.1
    mreexdomd.8
    mrissd
    cX
    dif0
    #
    syl6sseqr
    wph
    cT
    cX
    @6
    mreexdomd.6
    @7
    syl6sseqr
    wph
    cS
    cT
    cN
    cfv
    cT
    c0
    cun
    #
    cN
    cfv
    mreexdomd.5
    @8
    cT
    cN
    cT
    un0
    fveq2i
    syl6sseqr
    wph
    cS
    c0
    cun
    cS
    cI
    cS
    un0
    mreexdomd.8
    syl5eqel
    mreexdomd.7
    mreexexd
    wph
    @0
    @5
    wcel
    #
    @3
    wa
    #
    wa
    #
    @1
    @0
    cT
    cdom
    wbr
    #
    @4
    wph
    @9
    @1
    @2
    simprrl
    @11
    @0
    cT
    wss
    #
    @12
    @11
    @0
    cT
    wph
    @9
    @3
    simprl
    elpwid
    wph
    @13
    @12
    wi
    #
    @10
    wph
    cT
    cvv
    wcel
    @14
    wph
    cT
    cX
    cvv
    wph
    cA
    cmre
    cX
    mreexdomd.1
    elfvexd
    mreexdomd.6
    ssexd
    @0
    cT
    cvv
    ssdomg
    syl
    adantr
    mpd
    cS
    @0
    cT
    endomtr
    syl2anc
    rexlimddv
end
