include "cvv.mm"
include "wcel.mm"
include "csmblfn.mm"
include "cfv.mm"
include "cmbf.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "wex.mm"
include "cr.mm"
include "cc0.mm"
include "0red.mm"
include "fmptd.mm"
include "reex.mm"
include "a1i.mm"
include "ssexd.mm"
include "fexd.mm"
include "smfmbfcex.mm"
include "wceq.mm"
include "eleq1.mm"
include "notbid.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "sylc.mm"

theorem nsssmfmbflem
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let vf: setvar f
  let cF: class F
  let cX: class X
  let vk: setvar k
  assume nsssmfmbflem.s: |- S = dom vol
  assume nsssmfmbflem.x: |- ( ph -> X C_ RR )
  assume nsssmfmbflem.n: |- ( ph -> -. X e. S )
  assume nsssmfmbflem.f: |- F = ( x e. X |-> 0 )

  disjoint F f
  disjoint S f
  disjoint X x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> E. f ( f e. ( SMblFn ` S ) /\ -. f e. MblFn ) )

  proof
    wph
    cF
    cvv
    wcel
    cF
    cS
    csmblfn
    cfv
    #
    wcel
    #
    cF
    cmbf
    wcel
    #
    wn
    #
    wa
    #
    vf
    cv
    #
    @0
    wcel
    #
    @5
    cmbf
    wcel
    #
    wn
    #
    wa
    #
    vf
    wex
    wph
    cX
    cr
    cvv
    cF
    wph
    vx
    cX
    cc0
    cr
    cF
    wph
    vx
    cv
    cX
    wcel
    wa
    0red
    nsssmfmbflem.f
    fmptd
    wph
    cX
    cr
    cvv
    cr
    cvv
    wcel
    wph
    reex
    a1i
    nsssmfmbflem.x
    ssexd
    fexd
    wph
    vx
    cS
    cF
    cX
    nsssmfmbflem.s
    nsssmfmbflem.x
    nsssmfmbflem.n
    nsssmfmbflem.f
    smfmbfcex
    @9
    @4
    vf
    cF
    cvv
    @5
    cF
    wceq
    #
    @6
    @1
    @8
    @3
    @5
    cF
    @0
    eleq1
    @10
    @7
    @2
    @5
    cF
    cmbf
    eleq1
    notbid
    anbi12d
    spcegv
    sylc
end
