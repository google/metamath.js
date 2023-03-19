include "cc0.mm"
include "cfv.mm"
include "cpi.mm"
include "wceq.mm"
include "c1.mm"
include "c2.mm"
include "cuz.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "cmul.mm"
include "wi.mm"
include "cn0.mm"
include "0nn0.mm"
include "cioo.mm"
include "cv.mm"
include "csin.mm"
include "cexp.mm"
include "citg.mm"
include "wa.mm"
include "oveq2.mm"
include "adantr.mm"
include "cc.mm"
include "ioosscn.mm"
include "sseli.mm"
include "sincld.mm"
include "adantl.mm"
include "exp0d.mm"
include "eqtrd.mm"
include "itgeq2dv.mm"
include "cvol.mm"
include "cdm.mm"
include "cr.mm"
include "ioombl.mm"
include "0re.mm"
include "pire.mm"
include "ioovolcl.mm"
include "mp2an.mm"
include "ax-1cn.mm"
include "itgconst.mm"
include "mp3an.mm"
include "recni.mm"
include "mulid2i.mm"
include "cle.mm"
include "wbr.mm"
include "pipos.mm"
include "ltleii.mm"
include "volioo.mm"
include "subid1i.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "elexi.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "1nn0.mm"
include "simpl.mm"
include "oveq2d.mm"
include "exp1d.mm"
include "itgex.mm"
include "itgsin0pi.mm"
include "id.mm"
include "itgsinexp.mm"
include "3pm3.2i.mm"

theorem wallispilem2
  let vx: setvar x
  let vn: setvar n
  let cI: class I
  let cN: class N
  let vk: setvar k
  assume wallispilem2.1: |- I = ( n e. NN0 |-> S. ( 0 (,) _pi ) ( ( sin ` x ) ^ n ) _d x )

  disjoint n x
  disjoint N n
  disjoint N x
  disjoint k x
  assert |- ( ( I ` 0 ) = _pi /\ ( I ` 1 ) = 2 /\ ( N e. ( ZZ>= ` 2 ) -> ( I ` N ) = ( ( ( N - 1 ) / N ) x. ( I ` ( N - 2 ) ) ) ) )

  proof
    cc0
    cI
    cfv
    cpi
    wceq
    #
    c1
    cI
    cfv
    #
    c2
    wceq
    cN
    c2
    cuz
    cfv
    wcel
    #
    cN
    cI
    cfv
    cN
    c1
    cmin
    co
    cN
    cdiv
    co
    cN
    c2
    cmin
    co
    cI
    cfv
    cmul
    co
    wceq
    wi
    cc0
    cn0
    wcel
    @0
    0nn0
    vn
    cc0
    vx
    cc0
    cpi
    cioo
    co
    #
    vx
    cv
    #
    csin
    cfv
    #
    vn
    cv
    #
    cexp
    co
    #
    citg
    #
    cpi
    cn0
    cI
    @6
    cc0
    wceq
    #
    @8
    vx
    @3
    c1
    citg
    #
    cpi
    @9
    vx
    @3
    @7
    c1
    @9
    @4
    @3
    wcel
    #
    wa
    #
    @7
    @5
    cc0
    cexp
    co
    #
    c1
    @9
    @7
    @13
    wceq
    @11
    @6
    cc0
    @5
    cexp
    oveq2
    adantr
    @12
    @5
    @11
    @5
    cc
    wcel
    #
    @9
    @11
    @4
    @3
    cc
    @4
    cc0
    cpi
    ioosscn
    sseli
    sincld
    #
    adantl
    exp0d
    eqtrd
    itgeq2dv
    @10
    c1
    @3
    cvol
    cfv
    #
    cmul
    co
    #
    cpi
    @3
    cvol
    cdm
    wcel
    @16
    cr
    wcel
    #
    c1
    cc
    wcel
    @10
    @17
    wceq
    cc0
    cpi
    ioombl
    cc0
    cr
    wcel
    #
    cpi
    cr
    wcel
    #
    @18
    0re
    pire
    cc0
    cpi
    ioovolcl
    mp2an
    #
    ax-1cn
    vx
    @3
    c1
    itgconst
    mp3an
    @17
    @16
    cpi
    @16
    @16
    @21
    recni
    mulid2i
    @16
    cpi
    cc0
    cmin
    co
    #
    cpi
    @19
    @20
    cc0
    cpi
    cle
    wbr
    @16
    @22
    wceq
    0re
    pire
    cc0
    cpi
    0re
    pire
    pipos
    ltleii
    cc0
    cpi
    volioo
    mp3an
    cpi
    cpi
    pire
    recni
    subid1i
    eqtri
    eqtri
    eqtri
    syl6eq
    wallispilem2.1
    cpi
    cr
    pire
    elexi
    fvmpt
    ax-mp
    @1
    vx
    @3
    @5
    citg
    #
    c2
    c1
    cn0
    wcel
    @1
    @23
    wceq
    1nn0
    vn
    c1
    @8
    @23
    cn0
    cI
    @6
    c1
    wceq
    #
    vx
    @3
    @7
    @5
    @24
    @11
    wa
    #
    @7
    @5
    c1
    cexp
    co
    @5
    @25
    @6
    c1
    @5
    cexp
    @24
    @11
    simpl
    oveq2d
    @25
    @5
    @11
    @14
    @24
    @15
    adantl
    exp1d
    eqtrd
    itgeq2dv
    wallispilem2.1
    vx
    @3
    @5
    itgex
    fvmpt
    ax-mp
    vx
    itgsin0pi
    eqtri
    @2
    vx
    vn
    cI
    cN
    wallispilem2.1
    @2
    id
    itgsinexp
    3pm3.2i
end
