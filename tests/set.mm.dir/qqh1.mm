include "cdr.mm"
include "wcel.mm"
include "cchr.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "c1.mm"
include "cqqh.mm"
include "cnumer.mm"
include "cdenom.mm"
include "co.mm"
include "cur.mm"
include "cq.mm"
include "cz.mm"
include "zssq.mm"
include "1z.mm"
include "sselii.mm"
include "qqhvval.mm"
include "mpan2.mm"
include "cgcd.mm"
include "cdiv.mm"
include "gcd1.mm"
include "ax-mp.mm"
include "1div1e1.mm"
include "eqcomi.mm"
include "pm3.2i.mm"
include "cn.mm"
include "wb.mm"
include "1nn.mm"
include "qnumdenbi.mm"
include "mp3an.mm"
include "mpbi.mm"
include "simpli.mm"
include "fveq2i.mm"
include "simpri.mm"
include "oveq12i.mm"
include "crg.mm"
include "drngring.mm"
include "eqid.mm"
include "zrh1.mm"
include "oveq12d.mm"
include "syl.mm"
include "ringidcl.mm"
include "dvr1.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "adantr.mm"

theorem qqh1
  let cB: class B
  let c.dv: class ./
  let cR: class R
  let cL: class L
  let ve: setvar e
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let cQ: class Q
  assume qqhval2.0: |- B = ( Base ` R )
  assume qqhval2.1: |- ./ = ( /r ` R )
  assume qqhval2.2: |- L = ( ZRHom ` R )


  assert |- ( ( R e. DivRing /\ ( chr ` R ) = 0 ) -> ( ( QQHom ` R ) ` 1 ) = ( 1r ` R ) )

  proof
    cR
    cdr
    wcel
    #
    cR
    cchr
    cfv
    cc0
    wceq
    #
    wa
    #
    c1
    cR
    cqqh
    cfv
    cfv
    #
    c1
    cnumer
    cfv
    #
    cL
    cfv
    #
    c1
    cdenom
    cfv
    #
    cL
    cfv
    #
    c.dv
    co
    #
    cR
    cur
    cfv
    #
    @2
    c1
    cq
    wcel
    #
    @3
    @8
    wceq
    cz
    cq
    c1
    zssq
    1z
    sselii
    #
    cB
    c.dv
    c1
    cR
    cL
    qqhval2.0
    qqhval2.1
    qqhval2.2
    qqhvval
    mpan2
    @0
    @8
    @9
    wceq
    @1
    @0
    @8
    c1
    cL
    cfv
    #
    @12
    c.dv
    co
    #
    @9
    @5
    @12
    @7
    @12
    c.dv
    @4
    c1
    cL
    @4
    c1
    wceq
    #
    @6
    c1
    wceq
    #
    c1
    c1
    cgcd
    co
    c1
    wceq
    #
    c1
    c1
    c1
    cdiv
    co
    #
    wceq
    #
    wa
    #
    @14
    @15
    wa
    #
    @16
    @18
    c1
    cz
    wcel
    #
    @16
    1z
    c1
    gcd1
    ax-mp
    @17
    c1
    1div1e1
    eqcomi
    pm3.2i
    @10
    @21
    c1
    cn
    wcel
    @19
    @20
    wb
    @11
    1z
    1nn
    c1
    c1
    c1
    qnumdenbi
    mp3an
    mpbi
    #
    simpli
    fveq2i
    @6
    c1
    cL
    @14
    @15
    @22
    simpri
    fveq2i
    oveq12i
    @0
    @13
    @9
    @9
    c.dv
    co
    #
    @9
    @0
    cR
    crg
    wcel
    #
    @13
    @23
    wceq
    cR
    drngring
    #
    @24
    @12
    @9
    @12
    @9
    c.dv
    cR
    @9
    cL
    qqhval2.2
    @9
    eqid
    #
    zrh1
    #
    @27
    oveq12d
    syl
    @0
    @24
    @9
    cB
    wcel
    #
    @23
    @9
    wceq
    @25
    @0
    @24
    @28
    @25
    cB
    cR
    @9
    qqhval2.0
    @26
    ringidcl
    syl
    cB
    c.dv
    cR
    @9
    @9
    qqhval2.0
    qqhval2.1
    @26
    dvr1
    syl2anc
    eqtrd
    syl5eq
    adantr
    eqtrd
end
