include "crrx.mm"
include "cfv.mm"
include "cds.mm"
include "cr.mm"
include "cmap.mm"
include "co.mm"
include "cme.mm"
include "cv.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "csqrt.mm"
include "cmpt2.mm"
include "wceq.mm"
include "a1i.mm"
include "cfn.mm"
include "wcel.mm"
include "eqid.mm"
include "rrxdsfi.mm"
include "syl.mm"
include "eqtr4d.mm"
include "rrxmetfi.mm"
include "eqeltrd.mm"

theorem rrndsmet
  let wph: wff ph
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let cX: class X
  let vx: setvar x
  assume rrndsmet.1: |- ( ph -> X e. Fin )
  assume rrndsmet.2: |- D = ( f e. ( RR ^m X ) , g e. ( RR ^m X ) |-> ( sqrt ` sum_ k e. X ( ( ( f ` k ) - ( g ` k ) ) ^ 2 ) ) )

  disjoint X f
  disjoint X g
  disjoint X k
  disjoint f g
  disjoint f k
  disjoint g k
  disjoint k x
  assert |- ( ph -> D e. ( Met ` ( RR ^m X ) ) )

  proof
    wph
    cD
    cX
    crrx
    cfv
    #
    cds
    cfv
    #
    cr
    cX
    cmap
    co
    #
    cme
    cfv
    #
    wph
    cD
    vf
    vg
    @2
    @2
    cX
    vk
    cv
    #
    vf
    cv
    cfv
    @4
    vg
    cv
    cfv
    cmin
    co
    c2
    cexp
    co
    vk
    csu
    csqrt
    cfv
    cmpt2
    #
    @1
    cD
    @5
    wceq
    wph
    rrndsmet.2
    a1i
    wph
    cX
    cfn
    wcel
    #
    @1
    @5
    wceq
    rrndsmet.1
    @2
    vf
    vg
    vk
    @0
    cX
    @0
    eqid
    @2
    eqid
    rrxdsfi
    syl
    eqtr4d
    wph
    @6
    @1
    @3
    wcel
    rrndsmet.1
    @1
    cX
    @1
    eqid
    rrxmetfi
    syl
    eqeltrd
end
