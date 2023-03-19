include "cr.mm"
include "caddc.mm"
include "cn0.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cc0.mm"
include "cvv.mm"
include "wcel.mm"
include "reex.mm"
include "a1i.mm"
include "cuz.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "wceq.mm"
include "eqid.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "cbvmptv.mm"
include "mpteq2dv.mm"
include "adantl.mm"
include "eqtrd.mm"
include "elfznn0.mm"
include "mptex.mm"
include "fvmptd.mm"
include "seqof.mm"

theorem knoppcnlem7
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cC: class C
  let cT: class T
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cN: class N
  let vk: setvar k
  assume knoppcnlem7.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppcnlem7.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppcnlem7.n: |- ( ph -> N e. NN )
  assume knoppcnlem7.1: |- ( ph -> C e. RR )
  assume knoppcnlem7.2: |- ( ph -> M e. NN0 )

  disjoint F m
  disjoint F w
  disjoint F z
  disjoint m w
  disjoint m z
  disjoint w z
  disjoint M m
  disjoint M w
  disjoint m ph
  disjoint ph w
  disjoint F k
  disjoint k m
  disjoint k w
  disjoint k z
  disjoint M k
  disjoint k ph
  assert |- ( ph -> ( seq 0 ( oF + , ( m e. NN0 |-> ( z e. RR |-> ( ( F ` z ) ` m ) ) ) ) ` M ) = ( w e. RR |-> ( seq 0 ( + , ( F ` w ) ) ` M ) ) )

  proof
    wph
    vk
    vw
    cr
    caddc
    vm
    cn0
    vz
    cr
    vm
    cv
    #
    vz
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    #
    cmpt
    #
    vw
    cv
    #
    cF
    cfv
    #
    cc0
    cM
    cvv
    cr
    cvv
    wcel
    wph
    reex
    a1i
    wph
    cM
    cn0
    wcel
    cM
    cc0
    cuz
    cfv
    wcel
    knoppcnlem7.2
    cM
    elnn0uz
    sylib
    wph
    vk
    cv
    #
    cc0
    cM
    cfz
    co
    wcel
    #
    wa
    #
    vm
    @8
    @4
    vw
    cr
    @8
    @7
    cfv
    #
    cmpt
    #
    cn0
    @5
    cvv
    @5
    @5
    wceq
    @10
    @5
    eqid
    a1i
    @10
    @0
    @8
    wceq
    #
    wa
    #
    @4
    vw
    cr
    @0
    @7
    cfv
    #
    cmpt
    #
    @12
    @4
    @16
    wceq
    @14
    vz
    vw
    cr
    @3
    @15
    @1
    @6
    wceq
    @0
    @2
    @7
    @1
    @6
    cF
    fveq2
    fveq1d
    cbvmptv
    a1i
    @13
    @16
    @12
    wceq
    @10
    @13
    vw
    cr
    @15
    @11
    @0
    @8
    @7
    fveq2
    mpteq2dv
    adantl
    eqtrd
    @9
    @8
    cn0
    wcel
    wph
    @8
    cM
    elfznn0
    adantl
    @12
    cvv
    wcel
    @10
    vw
    cr
    @11
    reex
    mptex
    a1i
    fvmptd
    seqof
end
