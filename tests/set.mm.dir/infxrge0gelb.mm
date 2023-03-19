include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "clt.mm"
include "cinf.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "wrex.mm"
include "cle.mm"
include "wral.mm"
include "infxrge0glb.mm"
include "notbid.mm"
include "cxr.mm"
include "iccssxr.mm"
include "sseldi.mm"
include "wor.mm"
include "wss.mm"
include "xrltso.mm"
include "soss.mm"
include "mp2.mm"
include "a1i.mm"
include "wi.mm"
include "wa.mm"
include "xrge0infss.mm"
include "syl.mm"
include "infcl.mm"
include "xrlenltd.mm"
include "wcel.mm"
include "adantr.mm"
include "syl6ss.mm"
include "sselda.mm"
include "ralbidva.mm"
include "ralnex.mm"
include "syl6bb.mm"
include "3bitr4d.mm"

theorem infxrge0gelb
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  assume infxrge0glb.a: |- ( ph -> A C_ ( 0 [,] +oo ) )
  assume infxrge0glb.b: |- ( ph -> B e. ( 0 [,] +oo ) )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint ph z
  assert |- ( ph -> ( B <_ inf ( A , ( 0 [,] +oo ) , < ) <-> A. x e. A B <_ x ) )

  proof
    wph
    cA
    cc0
    cpnf
    cicc
    co
    #
    clt
    cinf
    #
    cB
    clt
    wbr
    #
    wn
    vx
    cv
    #
    cB
    clt
    wbr
    #
    vx
    cA
    wrex
    #
    wn
    #
    cB
    @1
    cle
    wbr
    cB
    @3
    cle
    wbr
    #
    vx
    cA
    wral
    #
    wph
    @2
    @5
    wph
    vx
    cA
    cB
    infxrge0glb.a
    infxrge0glb.b
    infxrge0glb
    notbid
    wph
    cB
    @1
    wph
    @0
    cxr
    cB
    cc0
    cpnf
    iccssxr
    #
    infxrge0glb.b
    sseldi
    #
    wph
    @0
    cxr
    @1
    @9
    wph
    vx
    vy
    vz
    @0
    cA
    clt
    @0
    clt
    wor
    #
    wph
    @0
    cxr
    wss
    cxr
    clt
    wor
    @11
    @9
    xrltso
    @0
    cxr
    clt
    soss
    mp2
    a1i
    wph
    cA
    @0
    wss
    vy
    cv
    #
    @3
    clt
    wbr
    wn
    vy
    cA
    wral
    @3
    @12
    clt
    wbr
    vz
    cv
    @12
    clt
    wbr
    vz
    cA
    wrex
    wi
    vy
    @0
    wral
    wa
    vx
    @0
    wrex
    infxrge0glb.a
    vx
    vy
    vz
    cA
    xrge0infss
    syl
    infcl
    sseldi
    xrlenltd
    wph
    @8
    @4
    wn
    #
    vx
    cA
    wral
    @6
    wph
    @7
    @13
    vx
    cA
    wph
    @3
    cA
    wcel
    #
    wa
    cB
    @3
    wph
    cB
    cxr
    wcel
    @14
    @10
    adantr
    wph
    cA
    cxr
    @3
    wph
    cA
    @0
    cxr
    infxrge0glb.a
    @9
    syl6ss
    sselda
    xrlenltd
    ralbidva
    @4
    vx
    cA
    ralnex
    syl6bb
    3bitr4d
end
