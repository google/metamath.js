include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "ciun.mm"
include "cn.mm"
include "cv.mm"
include "c0.mm"
include "cif.mm"
include "cun.mm"
include "cdif.mm"
include "iunxun.mm"
include "wceq.mm"
include "wss.mm"
include "fzossnn.mm"
include "undif.mm"
include "mpbi.mm"
include "iuneq1.mm"
include "ax-mp.mm"
include "iftrue.mm"
include "iuneq2i.mm"
include "eldifn.mm"
include "iffalsed.mm"
include "iun0.mm"
include "eqtri.mm"
include "uneq12i.mm"
include "3eqtr3i.mm"
include "un0.mm"
include "0elsiga.mm"
include "wi.mm"
include "simpr.mm"
include "simpllr.mm"
include "mpd.mm"
include "wn.mm"
include "simplll.mm"
include "ifclda.mm"
include "exp31.mm"
include "ralimdv2.mm"
include "imp.mm"
include "sylan.mm"
include "sigaclcu2.mm"
include "syldan.mm"
include "syl5eqelr.mm"

theorem sigaclfu2
  let cA: class A
  let cS: class S
  let vk: setvar k
  let cN: class N
  let vo: setvar o
  let vs: setvar s
  let vx: setvar x

  disjoint S k
  disjoint N k
  disjoint o s
  disjoint o x
  disjoint S o
  disjoint s x
  disjoint S s
  disjoint S x
  disjoint A x
  disjoint k x
  assert |- ( ( S e. U. ran sigAlgebra /\ A. k e. ( 1 ..^ N ) A e. S ) -> U_ k e. ( 1 ..^ N ) A e. S )

  proof
    cS
    csiga
    crn
    cuni
    wcel
    #
    cA
    cS
    wcel
    #
    vk
    c1
    cN
    cfzo
    co
    #
    wral
    #
    wa
    vk
    @2
    cA
    ciun
    #
    vk
    cn
    vk
    cv
    #
    @2
    wcel
    #
    cA
    c0
    cif
    #
    ciun
    #
    cS
    @8
    @4
    c0
    cun
    #
    @4
    vk
    @2
    cn
    @2
    cdif
    #
    cun
    #
    @7
    ciun
    #
    vk
    @2
    @7
    ciun
    #
    vk
    @10
    @7
    ciun
    #
    cun
    @8
    @9
    vk
    @2
    @10
    @7
    iunxun
    @11
    cn
    wceq
    #
    @12
    @8
    wceq
    @2
    cn
    wss
    @15
    cN
    fzossnn
    @2
    cn
    undif
    mpbi
    vk
    @11
    cn
    @7
    iuneq1
    ax-mp
    @13
    @4
    @14
    c0
    vk
    @2
    @7
    cA
    @6
    cA
    c0
    iftrue
    iuneq2i
    @14
    vk
    @10
    c0
    ciun
    c0
    vk
    @10
    @7
    c0
    @5
    @10
    wcel
    @6
    cA
    c0
    @5
    cn
    @2
    eldifn
    iffalsed
    iuneq2i
    vk
    @10
    iun0
    eqtri
    uneq12i
    3eqtr3i
    @4
    un0
    eqtri
    @0
    @3
    @7
    cS
    wcel
    #
    vk
    cn
    wral
    #
    @8
    cS
    wcel
    @0
    c0
    cS
    wcel
    #
    @3
    @17
    cS
    0elsiga
    @18
    @3
    @17
    @18
    @1
    @16
    vk
    @2
    cn
    @18
    @6
    @1
    wi
    #
    @5
    cn
    wcel
    #
    @16
    @18
    @19
    wa
    @20
    wa
    #
    @6
    cA
    c0
    cS
    @21
    @6
    wa
    @6
    @1
    @21
    @6
    simpr
    @18
    @19
    @20
    @6
    simpllr
    mpd
    @18
    @19
    @20
    @6
    wn
    simplll
    ifclda
    exp31
    ralimdv2
    imp
    sylan
    @7
    cS
    vk
    sigaclcu2
    syldan
    syl5eqelr
end
