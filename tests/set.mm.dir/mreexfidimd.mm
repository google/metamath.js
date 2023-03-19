include "cdom.mm"
include "wbr.mm"
include "cen.mm"
include "cfv.mm"
include "mrissd.mm"
include "mrcssidd.mm"
include "sseqtrd.mm"
include "cfn.mm"
include "wcel.mm"
include "orcd.mm"
include "mreexdomd.mm"
include "sseqtr4d.mm"
include "olcd.mm"
include "sbth.mm"
include "syl2anc.mm"

theorem mreexfidimd
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
  assume mreexfidimd.1: |- ( ph -> A e. ( Moore ` X ) )
  assume mreexfidimd.2: |- N = ( mrCls ` A )
  assume mreexfidimd.3: |- I = ( mrInd ` A )
  assume mreexfidimd.4: |- ( ph -> A. s e. ~P X A. y e. X A. z e. ( ( N ` ( s u. { y } ) ) \ ( N ` s ) ) y e. ( N ` ( s u. { z } ) ) )
  assume mreexfidimd.5: |- ( ph -> S e. I )
  assume mreexfidimd.6: |- ( ph -> T e. I )
  assume mreexfidimd.7: |- ( ph -> S e. Fin )
  assume mreexfidimd.8: |- ( ph -> ( N ` S ) = ( N ` T ) )

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
  assert |- ( ph -> S ~~ T )

  proof
    wph
    cS
    cT
    cdom
    wbr
    cT
    cS
    cdom
    wbr
    cS
    cT
    cen
    wbr
    wph
    vy
    vz
    cA
    cS
    cT
    cI
    cN
    cX
    vs
    mreexfidimd.1
    mreexfidimd.2
    mreexfidimd.3
    mreexfidimd.4
    wph
    cS
    cS
    cN
    cfv
    #
    cT
    cN
    cfv
    #
    wph
    cA
    cS
    cN
    cX
    mreexfidimd.1
    mreexfidimd.2
    wph
    cA
    cS
    cI
    cX
    mreexfidimd.3
    mreexfidimd.1
    mreexfidimd.5
    mrissd
    #
    mrcssidd
    mreexfidimd.8
    sseqtrd
    wph
    cA
    cT
    cI
    cX
    mreexfidimd.3
    mreexfidimd.1
    mreexfidimd.6
    mrissd
    #
    wph
    cS
    cfn
    wcel
    #
    cT
    cfn
    wcel
    #
    mreexfidimd.7
    orcd
    mreexfidimd.5
    mreexdomd
    wph
    vy
    vz
    cA
    cT
    cS
    cI
    cN
    cX
    vs
    mreexfidimd.1
    mreexfidimd.2
    mreexfidimd.3
    mreexfidimd.4
    wph
    cT
    @1
    @0
    wph
    cA
    cT
    cN
    cX
    mreexfidimd.1
    mreexfidimd.2
    @3
    mrcssidd
    mreexfidimd.8
    sseqtr4d
    @2
    wph
    @4
    @5
    mreexfidimd.7
    olcd
    mreexfidimd.6
    mreexdomd
    cS
    cT
    sbth
    syl2anc
end
