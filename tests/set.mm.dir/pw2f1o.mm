include "cpw.mm"
include "cpr.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "cif.mm"
include "cmpt.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cvv.mm"
include "wa.mm"
include "wceq.mm"
include "eqid.mm"
include "pw2f1olem.mm"
include "biimpa.mm"
include "mpanr2.mm"
include "simpld.mm"
include "vex.mm"
include "cnvex.mm"
include "imaex.mm"
include "a1i.mm"
include "f1od.mm"

theorem pw2f1o
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let cW: class W
  let vy: setvar y
  let cS: class S
  let cG: class G
  assume pw2f1o.1: |- ( ph -> A e. V )
  assume pw2f1o.2: |- ( ph -> B e. W )
  assume pw2f1o.3: |- ( ph -> C e. W )
  assume pw2f1o.4: |- ( ph -> B =/= C )
  assume pw2f1o.5: |- F = ( x e. ~P A |-> ( z e. A |-> if ( z e. x , C , B ) ) )

  disjoint x z
  disjoint A x
  disjoint A z
  disjoint B x
  disjoint B z
  disjoint C x
  disjoint C z
  disjoint ph x
  disjoint x y
  disjoint y z
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint ph y
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint G x
  disjoint G y
  assert |- ( ph -> F : ~P A -1-1-onto-> ( { B , C } ^m A ) )

  proof
    wph
    vx
    vy
    cA
    cpw
    #
    cB
    cC
    cpr
    cA
    cmap
    co
    #
    vz
    cA
    vz
    cv
    vx
    cv
    #
    wcel
    cC
    cB
    cif
    cmpt
    #
    vy
    cv
    #
    ccnv
    #
    cC
    csn
    #
    cima
    #
    cF
    @1
    cvv
    pw2f1o.5
    wph
    @2
    @0
    wcel
    #
    wa
    @3
    @1
    wcel
    #
    @2
    @3
    ccnv
    @6
    cima
    wceq
    #
    wph
    @8
    @3
    @3
    wceq
    #
    @9
    @10
    wa
    #
    @3
    eqid
    wph
    @8
    @11
    wa
    @12
    wph
    vz
    cA
    cB
    cC
    @2
    @3
    cV
    cW
    pw2f1o.1
    pw2f1o.2
    pw2f1o.3
    pw2f1o.4
    pw2f1olem
    biimpa
    mpanr2
    simpld
    @7
    cvv
    wcel
    wph
    @4
    @1
    wcel
    wa
    @5
    @6
    @4
    vy
    vex
    cnvex
    imaex
    a1i
    wph
    vz
    cA
    cB
    cC
    @2
    @4
    cV
    cW
    pw2f1o.1
    pw2f1o.2
    pw2f1o.3
    pw2f1o.4
    pw2f1olem
    f1od
end
