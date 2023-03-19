include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "wrex.mm"
include "wcel.mm"
include "wa.mm"
include "cxr.mm"
include "wb.mm"
include "cicc.mm"
include "co.mm"
include "iccssxr.mm"
include "syl6ss.mm"
include "sselda.mm"
include "sseldd.mm"
include "adantr.mm"
include "xrlenlt.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "nrexdv.mm"
include "supicclub.mm"
include "mtbird.mm"
include "supicc.mm"
include "sseldi.mm"
include "mpbird.mm"

theorem supicclub2
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  assume supicc.1: |- ( ph -> B e. RR )
  assume supicc.2: |- ( ph -> C e. RR )
  assume supicc.3: |- ( ph -> A C_ ( B [,] C ) )
  assume supicc.4: |- ( ph -> A =/= (/) )
  assume supiccub.1: |- ( ph -> D e. A )
  assume supicclub2.1: |- ( ( ph /\ z e. A ) -> z <_ D )

  disjoint A z
  disjoint D z
  disjoint ph z
  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint C x
  disjoint C y
  disjoint ph x
  assert |- ( ph -> sup ( A , RR , < ) <_ D )

  proof
    wph
    cA
    cr
    clt
    csup
    #
    cD
    cle
    wbr
    #
    cD
    @0
    clt
    wbr
    #
    wn
    #
    wph
    @2
    cD
    vz
    cv
    #
    clt
    wbr
    #
    vz
    cA
    wrex
    wph
    @5
    vz
    cA
    wph
    @4
    cA
    wcel
    #
    wa
    #
    @4
    cD
    cle
    wbr
    #
    @5
    wn
    #
    supicclub2.1
    @7
    @4
    cxr
    wcel
    cD
    cxr
    wcel
    #
    @8
    @9
    wb
    wph
    cA
    cxr
    @4
    wph
    cA
    cB
    cC
    cicc
    co
    #
    cxr
    supicc.3
    cB
    cC
    iccssxr
    #
    syl6ss
    #
    sselda
    wph
    @10
    @6
    wph
    cA
    cxr
    cD
    @13
    supiccub.1
    sseldd
    #
    adantr
    @4
    cD
    xrlenlt
    syl2anc
    mpbid
    nrexdv
    wph
    vz
    cA
    cB
    cC
    cD
    supicc.1
    supicc.2
    supicc.3
    supicc.4
    supiccub.1
    supicclub
    mtbird
    wph
    @0
    cxr
    wcel
    @10
    @1
    @3
    wb
    wph
    @11
    cxr
    @0
    @12
    wph
    cA
    cB
    cC
    supicc.1
    supicc.2
    supicc.3
    supicc.4
    supicc
    sseldi
    @14
    @0
    cD
    xrlenlt
    syl2anc
    mpbird
end
