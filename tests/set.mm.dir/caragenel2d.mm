include "cv.mm"
include "cpw.mm"
include "wcel.mm"
include "wa.mm"
include "cin.mm"
include "cfv.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "cxr.mm"
include "come.mm"
include "adantr.mm"
include "wss.mm"
include "inss1.mm"
include "elpwi.mm"
include "syl5ss.mm"
include "adantl.mm"
include "omexrcl.mm"
include "ssdifssd.mm"
include "xaddcl.mm"
include "syl2anc.mm"
include "omelesplit.mm"
include "xrletrid.mm"
include "carageneld.mm"

theorem caragenel2d
  let wph: wff ph
  let cS: class S
  let cE: class E
  let cO: class O
  let cX: class X
  let va: setvar a
  let vk: setvar k
  let vx: setvar x
  assume caragenel2d.o: |- ( ph -> O e. OutMeas )
  assume caragenel2d.x: |- X = U. dom O
  assume caragenel2d.s: |- S = ( CaraGen ` O )
  assume caragenel2d.e: |- ( ph -> E e. ~P X )
  assume caragenel2d.a: |- ( ( ph /\ a e. ~P X ) -> ( ( O ` ( a i^i E ) ) +e ( O ` ( a \ E ) ) ) <_ ( O ` a ) )

  disjoint E a
  disjoint O a
  disjoint a ph
  disjoint k x
  assert |- ( ph -> E e. S )

  proof
    wph
    cS
    cE
    cO
    cX
    va
    caragenel2d.o
    caragenel2d.x
    caragenel2d.s
    caragenel2d.e
    wph
    va
    cv
    #
    cX
    cpw
    wcel
    #
    wa
    #
    @0
    cE
    cin
    #
    cO
    cfv
    #
    @0
    cE
    cdif
    #
    cO
    cfv
    #
    cxad
    co
    #
    @0
    cO
    cfv
    @2
    @4
    cxr
    wcel
    @6
    cxr
    wcel
    @7
    cxr
    wcel
    @2
    @3
    cO
    cX
    wph
    cO
    come
    wcel
    @1
    caragenel2d.o
    adantr
    #
    caragenel2d.x
    @1
    @3
    cX
    wss
    wph
    @1
    @3
    @0
    cX
    @0
    cE
    inss1
    @0
    cX
    elpwi
    #
    syl5ss
    adantl
    omexrcl
    @2
    @5
    cO
    cX
    @8
    caragenel2d.x
    @1
    @5
    cX
    wss
    wph
    @1
    @0
    cX
    cE
    @9
    ssdifssd
    adantl
    omexrcl
    @4
    @6
    xaddcl
    syl2anc
    @2
    @0
    cO
    cX
    @8
    caragenel2d.x
    @1
    @0
    cX
    wss
    wph
    @9
    adantl
    #
    omexrcl
    caragenel2d.a
    @2
    @0
    cE
    cO
    cX
    @8
    caragenel2d.x
    @10
    omelesplit
    xrletrid
    carageneld
end
