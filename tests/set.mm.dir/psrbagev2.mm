include "cof.mm"
include "co.mm"
include "cvv.mm"
include "wf.mm"
include "cfsupp.mm"
include "wbr.mm"
include "psrbagev1.mm"
include "simpld.mm"
include "simprd.mm"
include "gsumcl.mm"

theorem psrbagev2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let c.x: class .x.
  let vh: setvar h
  let cG: class G
  let cI: class I
  let c.0: class .0.
  let vy: setvar y
  let vz: setvar z
  assume psrbagev1.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }
  assume psrbagev1.c: |- C = ( Base ` T )
  assume psrbagev1.x: |- .x. = ( .g ` T )
  assume psrbagev1.z: |- .0. = ( 0g ` T )
  assume psrbagev1.t: |- ( ph -> T e. CMnd )
  assume psrbagev1.b: |- ( ph -> B e. D )
  assume psrbagev1.g: |- ( ph -> G : I --> C )
  assume psrbagev1.i: |- ( ph -> I e. _V )

  disjoint B h
  disjoint I h
  disjoint ph y
  disjoint ph z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint C z
  disjoint G z
  disjoint .x. y
  disjoint .x. z
  disjoint .0. z
  assert |- ( ph -> ( T gsum ( B oF .x. G ) ) e. C )

  proof
    wph
    cI
    cC
    cB
    cG
    c.x
    cof
    co
    #
    cT
    cvv
    c.0
    psrbagev1.c
    psrbagev1.z
    psrbagev1.t
    psrbagev1.i
    wph
    cI
    cC
    @0
    wf
    #
    @0
    c.0
    cfsupp
    wbr
    #
    wph
    cB
    cC
    cD
    cT
    c.x
    vh
    cG
    cI
    c.0
    psrbagev1.d
    psrbagev1.c
    psrbagev1.x
    psrbagev1.z
    psrbagev1.t
    psrbagev1.b
    psrbagev1.g
    psrbagev1.i
    psrbagev1
    #
    simpld
    wph
    @1
    @2
    @3
    simprd
    gsumcl
end
