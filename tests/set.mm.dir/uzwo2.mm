include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wreu.mm"
include "uzwo.mm"
include "cr.mm"
include "cz.mm"
include "uzssz.mm"
include "zssre.mm"
include "sstri.mm"
include "sstr.mm"
include "mpan2.mm"
include "lbreu.mm"
include "sylan.mm"
include "syldan.mm"

theorem uzwo2
  let cS: class S
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let vh: setvar h
  let vt: setvar t
  let vn: setvar n
  let vm: setvar m

  disjoint j k
  disjoint S j
  disjoint S k
  disjoint h t
  disjoint h n
  disjoint h m
  disjoint M h
  disjoint n t
  disjoint m t
  disjoint M t
  disjoint m n
  disjoint M n
  disjoint M m
  disjoint h j
  disjoint h k
  disjoint S h
  disjoint j t
  disjoint j m
  disjoint j n
  disjoint k t
  disjoint S t
  disjoint k m
  disjoint k n
  disjoint S m
  disjoint S n
  assert |- ( ( S C_ ( ZZ>= ` M ) /\ S =/= (/) ) -> E! j e. S A. k e. S j <_ k )

  proof
    cS
    cM
    cuz
    cfv
    #
    wss
    #
    cS
    c0
    wne
    vj
    cv
    vk
    cv
    cle
    wbr
    vk
    cS
    wral
    #
    vj
    cS
    wrex
    #
    @2
    vj
    cS
    wreu
    #
    cS
    vj
    vk
    cM
    uzwo
    @1
    cS
    cr
    wss
    #
    @3
    @4
    @1
    @0
    cr
    wss
    @5
    @0
    cz
    cr
    cM
    uzssz
    zssre
    sstri
    cS
    @0
    cr
    sstr
    mpan2
    vj
    vk
    cS
    lbreu
    sylan
    syldan
end
