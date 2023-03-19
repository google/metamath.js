include "cdr.mm"
include "wcel.mm"
include "cchr.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cqqh.mm"
include "cnumer.mm"
include "cdenom.mm"
include "co.mm"
include "c0g.mm"
include "cq.mm"
include "cz.mm"
include "zssq.mm"
include "0z.mm"
include "sselii.mm"
include "qqhvval.mm"
include "mpan2.mm"
include "c1.mm"
include "cgcd.mm"
include "cdiv.mm"
include "cabs.mm"
include "1z.mm"
include "gcd0id.mm"
include "ax-mp.mm"
include "abs1.mm"
include "eqtri.mm"
include "0cn.mm"
include "div1i.mm"
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
include "cur.mm"
include "crg.mm"
include "drngring.mm"
include "eqid.mm"
include "zrh0.mm"
include "zrh1.mm"
include "oveq12d.mm"
include "syl.mm"
include "cgrp.mm"
include "drnggrp.mm"
include "grpidcl.mm"
include "dvr1.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "adantr.mm"

theorem qqh0
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


  assert |- ( ( R e. DivRing /\ ( chr ` R ) = 0 ) -> ( ( QQHom ` R ) ` 0 ) = ( 0g ` R ) )

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
    cc0
    cR
    cqqh
    cfv
    cfv
    #
    cc0
    cnumer
    cfv
    #
    cL
    cfv
    #
    cc0
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
    c0g
    cfv
    #
    @2
    cc0
    cq
    wcel
    #
    @3
    @8
    wceq
    cz
    cq
    cc0
    zssq
    0z
    sselii
    #
    cB
    c.dv
    cc0
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
    cc0
    cL
    cfv
    #
    c1
    cL
    cfv
    #
    c.dv
    co
    #
    @9
    @5
    @12
    @7
    @13
    c.dv
    @4
    cc0
    cL
    @4
    cc0
    wceq
    #
    @6
    c1
    wceq
    #
    cc0
    c1
    cgcd
    co
    #
    c1
    wceq
    #
    cc0
    cc0
    c1
    cdiv
    co
    #
    wceq
    #
    wa
    #
    @15
    @16
    wa
    #
    @18
    @20
    @17
    c1
    cabs
    cfv
    #
    c1
    c1
    cz
    wcel
    @17
    @23
    wceq
    1z
    c1
    gcd0id
    ax-mp
    abs1
    eqtri
    @19
    cc0
    cc0
    0cn
    div1i
    eqcomi
    pm3.2i
    @10
    cc0
    cz
    wcel
    c1
    cn
    wcel
    @21
    @22
    wb
    @11
    0z
    1nn
    cc0
    cc0
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
    @15
    @16
    @24
    simpri
    fveq2i
    oveq12i
    @0
    @14
    @9
    cR
    cur
    cfv
    #
    c.dv
    co
    #
    @9
    @0
    cR
    crg
    wcel
    #
    @14
    @26
    wceq
    cR
    drngring
    #
    @27
    @12
    @9
    @13
    @25
    c.dv
    cR
    cL
    @9
    qqhval2.2
    @9
    eqid
    #
    zrh0
    cR
    @25
    cL
    qqhval2.2
    @25
    eqid
    #
    zrh1
    oveq12d
    syl
    @0
    @27
    @9
    cB
    wcel
    #
    @26
    @9
    wceq
    @28
    @0
    cR
    cgrp
    wcel
    @31
    cR
    drnggrp
    cB
    cR
    @9
    qqhval2.0
    @29
    grpidcl
    syl
    cB
    c.dv
    cR
    @25
    @9
    qqhval2.0
    qqhval2.1
    @30
    dvr1
    syl2anc
    eqtrd
    syl5eq
    adantr
    eqtrd
end
