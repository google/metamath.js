include "clgam.mm"
include "cfv.mm"
include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "c1.mm"
include "cseq.mm"
include "clog.mm"
include "co.mm"
include "cli.mm"
include "wbr.mm"
include "cv.mm"
include "cabs.mm"
include "cle.mm"
include "cdiv.mm"
include "cn0.mm"
include "wral.mm"
include "wa.mm"
include "crab.mm"
include "eqid.mm"
include "lgamcvglem.mm"
include "simprd.mm"

theorem lgamcvg
  let wph: wff ph
  let cA: class A
  let vm: setvar m
  let cG: class G
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume lgamcvg.g: |- G = ( m e. NN |-> ( ( A x. ( log ` ( ( m + 1 ) / m ) ) ) - ( log ` ( ( A / m ) + 1 ) ) ) )
  assume lgamcvg.a: |- ( ph -> A e. ( CC \ ( ZZ \ NN ) ) )

  disjoint A m
  disjoint m ph
  disjoint k m
  disjoint k n
  disjoint k r
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m n
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint r x
  disjoint r y
  disjoint A r
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint G k
  disjoint G n
  disjoint G y
  disjoint k ph
  disjoint n ph
  disjoint ph r
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> seq 1 ( + , G ) ~~> ( ( log_G ` A ) + ( log ` A ) ) )

  proof
    wph
    cA
    clgam
    cfv
    #
    cc
    wcel
    caddc
    cG
    c1
    cseq
    @0
    cA
    clog
    cfv
    caddc
    co
    cli
    wbr
    wph
    vx
    cA
    vx
    cv
    #
    cabs
    cfv
    vy
    cv
    #
    cle
    wbr
    c1
    @2
    cdiv
    co
    @1
    vk
    cv
    caddc
    co
    cabs
    cfv
    cle
    wbr
    vk
    cn0
    wral
    wa
    vx
    cc
    crab
    #
    vk
    vm
    cG
    vy
    @3
    eqid
    lgamcvg.a
    lgamcvg.g
    lgamcvglem
    simprd
end
