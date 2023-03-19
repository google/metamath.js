include "cv.mm"
include "csn.mm"
include "cun.mm"
include "cfv.mm"
include "wcel.mm"
include "cdif.mm"
include "wral.mm"
include "cpw.mm"
include "sselpwd.mm"
include "wceq.mm"
include "wa.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simpr.mm"
include "sneqd.mm"
include "uneq12d.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "wn.mm"
include "neleqtrrd.mm"
include "eldifd.mm"
include "simpllr.mm"
include "eleq12d.mm"
include "rspcdv.mm"
include "rspcimdv.mm"
include "mpd.mm"

theorem mreexd
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cS: class S
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vs: setvar s
  assume mreexd.1: |- ( ph -> X e. V )
  assume mreexd.2: |- ( ph -> A. s e. ~P X A. y e. X A. z e. ( ( N ` ( s u. { y } ) ) \ ( N ` s ) ) y e. ( N ` ( s u. { z } ) ) )
  assume mreexd.3: |- ( ph -> S C_ X )
  assume mreexd.4: |- ( ph -> Y e. X )
  assume mreexd.5: |- ( ph -> Z e. ( N ` ( S u. { Y } ) ) )
  assume mreexd.6: |- ( ph -> -. Z e. ( N ` S ) )

  disjoint X s
  disjoint s y
  disjoint X y
  disjoint S s
  disjoint s z
  disjoint S y
  disjoint S z
  disjoint y z
  disjoint ph s
  disjoint ph y
  disjoint ph z
  disjoint Y s
  disjoint Y y
  disjoint Y z
  disjoint Z s
  disjoint Z y
  disjoint Z z
  disjoint N s
  disjoint N y
  disjoint N z
  assert |- ( ph -> Y e. ( N ` ( S u. { Z } ) ) )

  proof
    wph
    vy
    cv
    #
    vs
    cv
    #
    vz
    cv
    #
    csn
    #
    cun
    #
    cN
    cfv
    #
    wcel
    #
    vz
    @1
    @0
    csn
    #
    cun
    #
    cN
    cfv
    #
    @1
    cN
    cfv
    #
    cdif
    #
    wral
    #
    vy
    cX
    wral
    #
    vs
    cX
    cpw
    #
    wral
    cY
    cS
    cZ
    csn
    #
    cun
    #
    cN
    cfv
    #
    wcel
    #
    mreexd.2
    wph
    @13
    @18
    vs
    cS
    @14
    wph
    cS
    cX
    cV
    mreexd.1
    mreexd.3
    sselpwd
    wph
    @1
    cS
    wceq
    #
    wa
    #
    @12
    @18
    vy
    cY
    cX
    wph
    cY
    cX
    wcel
    @19
    mreexd.4
    adantr
    @20
    @0
    cY
    wceq
    #
    wa
    #
    @6
    @18
    vz
    cZ
    @11
    @22
    cZ
    @9
    @10
    @22
    cZ
    cS
    cY
    csn
    #
    cun
    #
    cN
    cfv
    #
    @9
    wph
    cZ
    @25
    wcel
    @19
    @21
    mreexd.5
    ad2antrr
    @22
    @8
    @24
    cN
    @22
    @1
    cS
    @7
    @23
    wph
    @19
    @21
    simplr
    #
    @22
    @0
    cY
    @20
    @21
    simpr
    sneqd
    uneq12d
    fveq2d
    eleqtrrd
    @22
    @10
    cS
    cN
    cfv
    #
    cZ
    wph
    cZ
    @27
    wcel
    wn
    @19
    @21
    mreexd.6
    ad2antrr
    @22
    @1
    cS
    cN
    @26
    fveq2d
    neleqtrrd
    eldifd
    @22
    @2
    cZ
    wceq
    #
    wa
    #
    @0
    cY
    @5
    @17
    @20
    @21
    @28
    simplr
    @29
    @4
    @16
    cN
    @29
    @1
    cS
    @3
    @15
    wph
    @19
    @21
    @28
    simpllr
    @29
    @2
    cZ
    @22
    @28
    simpr
    sneqd
    uneq12d
    fveq2d
    eleq12d
    rspcdv
    rspcimdv
    rspcimdv
    mpd
end
