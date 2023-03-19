include "cc0.mm"
include "cv.mm"
include "cpjh.mm"
include "cfv.mm"
include "chod.mm"
include "co.mm"
include "csp.mm"
include "cle.mm"
include "wbr.mm"
include "chil.mm"
include "wral.mm"
include "cno.mm"
include "wss.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "cr.mm"
include "pjhcli.mm"
include "normcl.mm"
include "syl.mm"
include "resqcld.mm"
include "subge0d.mm"
include "cmv.mm"
include "wf.mm"
include "wceq.mm"
include "pjfi.mm"
include "hodval.mm"
include "mp3an12.mm"
include "oveq1d.mm"
include "id.mm"
include "his2sub.mm"
include "syl3anc.mm"
include "pjinormi.mm"
include "oveq12d.mm"
include "3eqtrd.mm"
include "breq2d.mm"
include "normge0.mm"
include "le2sqd.mm"
include "3bitr4d.mm"
include "ralbiia.mm"
include "pjnormssi.mm"
include "bitr4i.mm"

theorem pjssposi
  let vx: setvar x
  let cG: class G
  let cH: class H
  let vy: setvar y
  assume pjco.1: |- G e. CH
  assume pjco.2: |- H e. CH

  disjoint H x
  disjoint G x
  disjoint x y
  disjoint H y
  disjoint G y
  assert |- ( A. x e. ~H 0 <_ ( ( ( ( projh ` H ) -op ( projh ` G ) ) ` x ) .ih x ) <-> G C_ H )

  proof
    cc0
    vx
    cv
    #
    cH
    cpjh
    cfv
    #
    cG
    cpjh
    cfv
    #
    chod
    co
    cfv
    #
    @0
    csp
    co
    #
    cle
    wbr
    #
    vx
    chil
    wral
    @0
    @2
    cfv
    #
    cno
    cfv
    #
    @0
    @1
    cfv
    #
    cno
    cfv
    #
    cle
    wbr
    #
    vx
    chil
    wral
    cG
    cH
    wss
    @5
    @10
    vx
    chil
    @0
    chil
    wcel
    #
    cc0
    @9
    c2
    cexp
    co
    #
    @7
    c2
    cexp
    co
    #
    cmin
    co
    #
    cle
    wbr
    @13
    @12
    cle
    wbr
    @5
    @10
    @11
    @12
    @13
    @11
    @9
    @11
    @8
    chil
    wcel
    #
    @9
    cr
    wcel
    @0
    cH
    pjco.2
    pjhcli
    #
    @8
    normcl
    syl
    #
    resqcld
    @11
    @7
    @11
    @6
    chil
    wcel
    #
    @7
    cr
    wcel
    @0
    cG
    pjco.1
    pjhcli
    #
    @6
    normcl
    syl
    #
    resqcld
    subge0d
    @11
    @4
    @14
    cc0
    cle
    @11
    @4
    @8
    @6
    cmv
    co
    #
    @0
    csp
    co
    #
    @8
    @0
    csp
    co
    #
    @6
    @0
    csp
    co
    #
    cmin
    co
    #
    @14
    @11
    @3
    @21
    @0
    csp
    chil
    chil
    @1
    wf
    chil
    chil
    @2
    wf
    @11
    @3
    @21
    wceq
    cH
    pjco.2
    pjfi
    cG
    pjco.1
    pjfi
    @0
    @1
    @2
    hodval
    mp3an12
    oveq1d
    @11
    @15
    @18
    @11
    @22
    @25
    wceq
    @16
    @19
    @11
    id
    @8
    @6
    @0
    his2sub
    syl3anc
    @11
    @23
    @12
    @24
    @13
    cmin
    @0
    cH
    pjco.2
    pjinormi
    @0
    cG
    pjco.1
    pjinormi
    oveq12d
    3eqtrd
    breq2d
    @11
    @7
    @9
    @20
    @17
    @11
    @18
    cc0
    @7
    cle
    wbr
    @19
    @6
    normge0
    syl
    @11
    @15
    cc0
    @9
    cle
    wbr
    @16
    @8
    normge0
    syl
    le2sqd
    3bitr4d
    ralbiia
    vx
    cG
    cH
    pjco.1
    pjco.2
    pjnormssi
    bitr4i
end
