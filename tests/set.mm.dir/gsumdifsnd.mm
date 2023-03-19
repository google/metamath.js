include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "c0g.mm"
include "cfv.mm"
include "eqid.mm"
include "c0.mm"
include "cin.mm"
include "difid.mm"
include "wss.mm"
include "wceq.mm"
include "snssd.mm"
include "difin2.mm"
include "syl.mm"
include "syl5reqr.mm"
include "cun.mm"
include "wcel.mm"
include "difsnid.mm"
include "eqcomd.mm"
include "gsumsplit2.mm"
include "ccmn.mm"
include "cmnd.mm"
include "cmnmnd.mm"
include "gsumsnd.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem gsumdifsnd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let vk: setvar k
  let cG: class G
  let cM: class M
  let cW: class W
  let cX: class X
  let cY: class Y
  assume gsumdifsnd.b: |- B = ( Base ` G )
  assume gsumdifsnd.p: |- .+ = ( +g ` G )
  assume gsumdifsnd.g: |- ( ph -> G e. CMnd )
  assume gsumdifsnd.a: |- ( ph -> A e. W )
  assume gsumdifsnd.f: |- ( ph -> ( k e. A |-> X ) finSupp ( 0g ` G ) )
  assume gsumdifsnd.e: |- ( ( ph /\ k e. A ) -> X e. B )
  assume gsumdifsnd.m: |- ( ph -> M e. A )
  assume gsumdifsnd.y: |- ( ph -> Y e. B )
  assume gsumdifsnd.s: |- ( ( ph /\ k = M ) -> X = Y )

  disjoint A k
  disjoint B k
  disjoint G k
  disjoint M k
  disjoint k ph
  disjoint Y k
  assert |- ( ph -> ( G gsum ( k e. A |-> X ) ) = ( ( G gsum ( k e. ( A \ { M } ) |-> X ) ) .+ Y ) )

  proof
    wph
    cG
    vk
    cA
    cX
    cmpt
    cgsu
    co
    cG
    vk
    cA
    cM
    csn
    #
    cdif
    #
    cX
    cmpt
    cgsu
    co
    #
    cG
    vk
    @0
    cX
    cmpt
    cgsu
    co
    #
    c.pl
    co
    @2
    cY
    c.pl
    co
    wph
    cA
    cB
    @1
    @0
    c.pl
    vk
    cG
    cW
    cX
    cG
    c0g
    cfv
    #
    gsumdifsnd.b
    @4
    eqid
    gsumdifsnd.p
    gsumdifsnd.g
    gsumdifsnd.a
    gsumdifsnd.e
    gsumdifsnd.f
    wph
    c0
    @0
    @0
    cdif
    #
    @1
    @0
    cin
    #
    @0
    difid
    wph
    @0
    cA
    wss
    @5
    @6
    wceq
    wph
    cM
    cA
    gsumdifsnd.m
    snssd
    @0
    @0
    cA
    difin2
    syl
    syl5reqr
    wph
    @1
    @0
    cun
    #
    cA
    wph
    cM
    cA
    wcel
    @7
    cA
    wceq
    gsumdifsnd.m
    cA
    cM
    difsnid
    syl
    eqcomd
    gsumsplit2
    wph
    @3
    cY
    @2
    c.pl
    wph
    cX
    cB
    cY
    vk
    cG
    cM
    cA
    gsumdifsnd.b
    wph
    cG
    ccmn
    wcel
    cG
    cmnd
    wcel
    gsumdifsnd.g
    cG
    cmnmnd
    syl
    gsumdifsnd.m
    gsumdifsnd.y
    gsumdifsnd.s
    gsumsnd
    oveq2d
    eqtrd
end
