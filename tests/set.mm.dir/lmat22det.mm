include "cfv.mm"
include "c1.mm"
include "co.mm"
include "c2.mm"
include "crg.mm"
include "wcel.mm"
include "cfz.mm"
include "cmat.mm"
include "cbs.mm"
include "wceq.mm"
include "cs2.mm"
include "cn.mm"
include "2nn.mm"
include "a1i.mm"
include "cword.mm"
include "s2cld.mm"
include "chash.mm"
include "s2len.mm"
include "lmat22lem.mm"
include "eqid.mm"
include "lmatcl.mm"
include "caddc.mm"
include "cfzo.mm"
include "c3.mm"
include "cpr.mm"
include "cz.mm"
include "2z.mm"
include "fzval3.mm"
include "ax-mp.mm"
include "2p1e3.mm"
include "oveq2i.mm"
include "fzo13pr.mm"
include "3eqtri.mm"
include "m2detleib.mm"
include "syl2anc.mm"
include "lmat22e11.mm"
include "lmat22e22.mm"
include "oveq12d.mm"
include "lmat22e21.mm"
include "lmat22e12.mm"
include "eqtrd.mm"

theorem lmat22det
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cJ: class J
  let cM: class M
  let c.mi: class .-
  let cV: class V
  let vi: setvar i
  assume lmat22.m: |- M = ( litMat ` <" <" A B "> <" C D "> "> )
  assume lmat22.a: |- ( ph -> A e. V )
  assume lmat22.b: |- ( ph -> B e. V )
  assume lmat22.c: |- ( ph -> C e. V )
  assume lmat22.d: |- ( ph -> D e. V )
  assume lmat22det.t: |- .x. = ( .r ` R )
  assume lmat22det.s: |- .- = ( -g ` R )
  assume lmat22det.v: |- V = ( Base ` R )
  assume lmat22det.j: |- J = ( ( 1 ... 2 ) maDet R )
  assume lmat22det.r: |- ( ph -> R e. Ring )


  assert |- ( ph -> ( J ` M ) = ( ( A .x. D ) .- ( C .x. B ) ) )

  proof
    wph
    cM
    cJ
    cfv
    #
    c1
    c1
    cM
    co
    #
    c2
    c2
    cM
    co
    #
    c.x
    co
    #
    c2
    c1
    cM
    co
    #
    c1
    c2
    cM
    co
    #
    c.x
    co
    #
    c.mi
    co
    #
    cA
    cD
    c.x
    co
    #
    cC
    cB
    c.x
    co
    #
    c.mi
    co
    wph
    cR
    crg
    wcel
    cM
    c1
    c2
    cfz
    co
    #
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    @0
    @7
    wceq
    lmat22det.r
    wph
    @12
    cR
    vi
    cM
    c2
    @11
    cV
    cA
    cB
    cs2
    #
    cC
    cD
    cs2
    #
    cs2
    #
    crg
    lmat22.m
    c2
    cn
    wcel
    wph
    2nn
    a1i
    wph
    @13
    @14
    cV
    cword
    wph
    cA
    cB
    cV
    lmat22.a
    lmat22.b
    s2cld
    wph
    cC
    cD
    cV
    lmat22.c
    lmat22.d
    s2cld
    s2cld
    @15
    chash
    cfv
    c2
    wceq
    wph
    @13
    @14
    s2len
    a1i
    wph
    cA
    cB
    cC
    cD
    vi
    cM
    cV
    lmat22.m
    lmat22.a
    lmat22.b
    lmat22.c
    lmat22.d
    lmat22lem
    lmat22det.v
    @11
    eqid
    #
    @12
    eqid
    #
    lmat22det.r
    lmatcl
    @11
    @12
    cJ
    cR
    c.x
    cM
    c.mi
    @10
    @10
    c1
    c2
    c1
    caddc
    co
    #
    cfzo
    co
    #
    c1
    c3
    cfzo
    co
    c1
    c2
    cpr
    c2
    cz
    wcel
    @10
    @19
    wceq
    2z
    c1
    c2
    fzval3
    ax-mp
    @18
    c3
    c1
    cfzo
    2p1e3
    oveq2i
    fzo13pr
    3eqtri
    lmat22det.j
    @16
    @17
    lmat22det.s
    lmat22det.t
    m2detleib
    syl2anc
    wph
    @3
    @8
    @6
    @9
    c.mi
    wph
    @1
    cA
    @2
    cD
    c.x
    wph
    cA
    cB
    cC
    cD
    cM
    cV
    lmat22.m
    lmat22.a
    lmat22.b
    lmat22.c
    lmat22.d
    lmat22e11
    wph
    cA
    cB
    cC
    cD
    cM
    cV
    lmat22.m
    lmat22.a
    lmat22.b
    lmat22.c
    lmat22.d
    lmat22e22
    oveq12d
    wph
    @4
    cC
    @5
    cB
    c.x
    wph
    cA
    cB
    cC
    cD
    cM
    cV
    lmat22.m
    lmat22.a
    lmat22.b
    lmat22.c
    lmat22.d
    lmat22e21
    wph
    cA
    cB
    cC
    cD
    cM
    cV
    lmat22.m
    lmat22.a
    lmat22.b
    lmat22.c
    lmat22.d
    lmat22e12
    oveq12d
    oveq12d
    eqtrd
end
