include "cfn.mm"
include "wcel.mm"
include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "cmre.mm"
include "cfv.mm"
include "acsmred.mm"
include "adantr.mm"
include "cv.mm"
include "csn.mm"
include "cun.mm"
include "cdif.mm"
include "wral.mm"
include "cpw.mm"
include "simpr.mm"
include "wceq.mm"
include "mreexfidimd.mm"
include "wn.mm"
include "cacs.mm"
include "acsinfdimd.mm"
include "pm2.61dan.mm"

theorem acsexdimd
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
  assume acsexdimd.1: |- ( ph -> A e. ( ACS ` X ) )
  assume acsexdimd.2: |- N = ( mrCls ` A )
  assume acsexdimd.3: |- I = ( mrInd ` A )
  assume acsexdimd.4: |- ( ph -> A. s e. ~P X A. y e. X A. z e. ( ( N ` ( s u. { y } ) ) \ ( N ` s ) ) y e. ( N ` ( s u. { z } ) ) )
  assume acsexdimd.5: |- ( ph -> S e. I )
  assume acsexdimd.6: |- ( ph -> T e. I )
  assume acsexdimd.7: |- ( ph -> ( N ` S ) = ( N ` T ) )

  disjoint S s
  disjoint s y
  disjoint s z
  disjoint S y
  disjoint S z
  disjoint y z
  disjoint X s
  disjoint X y
  disjoint X z
  disjoint ph s
  disjoint ph y
  disjoint ph z
  disjoint I s
  disjoint I y
  disjoint I z
  disjoint N s
  disjoint N y
  disjoint N z
  assert |- ( ph -> S ~~ T )

  proof
    wph
    cS
    cfn
    wcel
    #
    cS
    cT
    cen
    wbr
    wph
    @0
    wa
    vy
    vz
    cA
    cS
    cT
    cI
    cN
    cX
    vs
    wph
    cA
    cX
    cmre
    cfv
    wcel
    @0
    wph
    cA
    cX
    acsexdimd.1
    acsmred
    adantr
    acsexdimd.2
    acsexdimd.3
    wph
    vy
    cv
    #
    vs
    cv
    #
    vz
    cv
    csn
    cun
    cN
    cfv
    wcel
    vz
    @2
    @1
    csn
    cun
    cN
    cfv
    @2
    cN
    cfv
    cdif
    wral
    vy
    cX
    wral
    vs
    cX
    cpw
    wral
    @0
    acsexdimd.4
    adantr
    wph
    cS
    cI
    wcel
    #
    @0
    acsexdimd.5
    adantr
    wph
    cT
    cI
    wcel
    #
    @0
    acsexdimd.6
    adantr
    wph
    @0
    simpr
    wph
    cS
    cN
    cfv
    cT
    cN
    cfv
    wceq
    #
    @0
    acsexdimd.7
    adantr
    mreexfidimd
    wph
    @0
    wn
    #
    wa
    cA
    cS
    cT
    cI
    cN
    cX
    wph
    cA
    cX
    cacs
    cfv
    wcel
    @6
    acsexdimd.1
    adantr
    acsexdimd.2
    acsexdimd.3
    wph
    @3
    @6
    acsexdimd.5
    adantr
    wph
    @4
    @6
    acsexdimd.6
    adantr
    wph
    @5
    @6
    acsexdimd.7
    adantr
    wph
    @6
    simpr
    acsinfdimd
    pm2.61dan
end
