include "cr.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cmpt.mm"
include "wcel.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "ifcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "hoidifhspval2.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem hoidifhspf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cD: class D
  let vk: setvar k
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  let va: setvar a
  assume hoidifhspf.d: |- D = ( x e. RR |-> ( a e. ( RR ^m X ) |-> ( k e. X |-> if ( k = K , if ( x <_ ( a ` k ) , ( a ` k ) , x ) , ( a ` k ) ) ) ) )
  assume hoidifhspf.y: |- ( ph -> Y e. RR )
  assume hoidifhspf.x: |- ( ph -> X e. V )
  assume hoidifhspf.a: |- ( ph -> A : X --> RR )

  disjoint A a
  disjoint A k
  disjoint a k
  disjoint K a
  disjoint K x
  disjoint a x
  disjoint X a
  disjoint X k
  disjoint X x
  disjoint k x
  disjoint Y a
  disjoint Y k
  disjoint Y x
  disjoint a ph
  disjoint k ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( ( D ` Y ) ` A ) : X --> RR )

  proof
    wph
    cX
    cr
    cA
    cY
    cD
    cfv
    cfv
    #
    wf
    cX
    cr
    vk
    cX
    vk
    cv
    #
    cK
    wceq
    #
    cY
    @1
    cA
    cfv
    #
    cle
    wbr
    #
    @3
    cY
    cif
    #
    @3
    cif
    #
    cmpt
    #
    wf
    wph
    vk
    cX
    @6
    cr
    @7
    wph
    @1
    cX
    wcel
    #
    wa
    #
    @2
    @5
    @3
    cr
    @9
    @4
    @3
    cY
    cr
    wph
    cX
    cr
    @1
    cA
    hoidifhspf.a
    ffvelrnda
    #
    wph
    cY
    cr
    wcel
    @8
    hoidifhspf.y
    adantr
    ifcld
    @10
    ifcld
    @7
    eqid
    fmptd
    wph
    cX
    cr
    @0
    @7
    wph
    vx
    cA
    cD
    vk
    cK
    cV
    cX
    cY
    va
    hoidifhspf.d
    hoidifhspf.y
    hoidifhspf.x
    hoidifhspf.a
    hoidifhspval2
    feq1d
    mpbird
end
